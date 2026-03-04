from collections import defaultdict

try:
    import pyslang
    from pyslang import SyntaxTree, SyntaxKind
except Exception:  # pragma: no cover - optional dependency
    pyslang = None
    SyntaxTree = None
    SyntaxKind = None

_COVERAGE_CACHE = {}


def _is_available():
    return pyslang is not None and SyntaxTree is not None and SyntaxKind is not None


def _assignment_kinds():
    if not _is_available():
        return set()
    kinds = set()
    for name in dir(SyntaxKind):
        if not name.endswith("AssignmentExpression"):
            continue
        if name == "AssignmentPatternExpression":
            continue
        kinds.add(getattr(SyntaxKind, name))
    return kinds


_ASSIGN_EXPR_KINDS = _assignment_kinds()


def _control_kinds():
    if not _is_available():
        return set()
    return {
        SyntaxKind.ConditionalStatement,
        SyntaxKind.CaseStatement,
        SyntaxKind.RandCaseStatement,
    }


_CONTROL_KINDS = _control_kinds()


def _extract_lhs_names(node):
    names = []

    def walk(n):
        if not isinstance(n, pyslang.SyntaxNode):
            return
        if n.kind in (SyntaxKind.IdentifierName, SyntaxKind.IdentifierSelectName):
            tok = n.identifier
            if tok is not None:
                names.append(tok.value)
            return
        if n.kind == SyntaxKind.ConcatenationExpression:
            for expr in n.expressions:
                walk(expr)
            return
        for child in n:
            if isinstance(child, pyslang.SyntaxNode):
                walk(child)

    walk(node)
    seen = set()
    uniq = []
    for name in names:
        if name not in seen:
            seen.add(name)
            uniq.append(name)
    return uniq


def _iter_module_decls(root):
    stack = [root]
    while stack:
        node = stack.pop()
        if not isinstance(node, pyslang.SyntaxNode):
            continue
        if node.kind == SyntaxKind.ModuleDeclaration:
            yield node
        for child in node:
            if isinstance(child, pyslang.SyntaxNode):
                stack.append(child)


def _collect_module_coverage(module_node, source_manager):
    stmt_map = defaultdict(set)
    branch_map = defaultdict(set)

    def line_of(node):
        return source_manager.getLineNumber(node.sourceRange.start)

    def add_coverage(names, stmt_line, control_lines):
        for name in names:
            stmt_map[name].add(stmt_line)
            for cline in control_lines:
                branch_map[name].add(cline)

    def visit(node, control_stack):
        if node.kind in _CONTROL_KINDS:
            control_stack.append(line_of(node))
            for child in node:
                if isinstance(child, pyslang.SyntaxNode):
                    visit(child, control_stack)
            control_stack.pop()
            return

        if node.kind == SyntaxKind.ExpressionStatement:
            expr = node.expr
            if expr is not None and expr.kind in _ASSIGN_EXPR_KINDS:
                names = _extract_lhs_names(expr.left)
                if names:
                    add_coverage(names, line_of(node), control_stack)
            return

        if node.kind == SyntaxKind.ContinuousAssign:
            assigns = getattr(node, "assignments", None)
            if assigns is not None:
                for item in assigns:
                    if isinstance(item, pyslang.SyntaxNode) and item.kind in _ASSIGN_EXPR_KINDS:
                        names = _extract_lhs_names(item.left)
                        if names:
                            add_coverage(names, line_of(item), control_stack)
            return

        for child in node:
            if isinstance(child, pyslang.SyntaxNode):
                visit(child, control_stack)

    visit(module_node, [])
    return stmt_map, branch_map


def build_coverage(verilog_files, include_dirs=None):
    if not _is_available():
        return None
    include_dirs = include_dirs or []
    key = (tuple(sorted(verilog_files)), tuple(sorted(include_dirs)))
    if key in _COVERAGE_CACHE:
        return _COVERAGE_CACHE[key]

    module_cov = {}

    for path in verilog_files:
        try:
            tree = SyntaxTree.fromFile(path)
        except Exception:
            continue
        root = tree.root
        sm = tree.sourceManager
        for module_node in _iter_module_decls(root):
            header = module_node.header
            if header is None or header.name is None:
                continue
            module_name = header.name.value
            stmt_map, branch_map = _collect_module_coverage(module_node, sm)
            if module_name in module_cov:
                # Merge if the same module name appears in multiple files.
                existing = module_cov[module_name]
                for var, lines in stmt_map.items():
                    existing["stmt"].setdefault(var, set()).update(lines)
                for var, lines in branch_map.items():
                    existing["branch"].setdefault(var, set()).update(lines)
            else:
                module_cov[module_name] = {
                    "file": path,
                    "stmt": stmt_map,
                    "branch": branch_map,
                }

    _COVERAGE_CACHE[key] = module_cov
    return module_cov
