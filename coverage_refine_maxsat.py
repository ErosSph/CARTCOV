import argparse
import re
import sys
import z3

# Optional import path: use the existing toolchain when available.
try:
    import proof_core_cegar as pcc
    from static_coi_extractor import extract_coi
    from slang_coverage import build_coverage as build_slang_coverage
    from pyslang import SyntaxTree, SyntaxKind, SyntaxNode
    import sva_to_smt as sva
except Exception:  # pragma: no cover - used only in core-refine mode
    pcc = None
    extract_coi = None
    build_slang_coverage = None
    SyntaxTree = None
    SyntaxKind = None
    SyntaxNode = None
    sva = None


def _strip_commands(text):
    lines = []
    skip_re = re.compile(r"^\s*\((check-sat|get-model|get-value|exit)")
    for line in text.splitlines():
        if skip_re.search(line):
            continue
        lines.append(line)
    return "\n".join(lines)


def _strip_comments(line):
    line = line.strip()
    if not line:
        return ""
    if line.startswith("#") or line.startswith("//"):
        return ""
    if "//" in line:
        line = line.split("//", 1)[0].strip()
    if "#" in line:
        line = line.split("#", 1)[0].strip()
    return line


def _load_hits(path):
    hits = []
    with open(path, "r", encoding="utf-8", errors="ignore") as handle:
        for raw in handle:
            line = _strip_comments(raw)
            if not line:
                continue
            if ":" in line:
                name, expr = line.split(":", 1)
            elif "=" in line:
                name, expr = line.split("=", 1)
            else:
                name = f"hit_{len(hits) + 1}"
                expr = line
            name = name.strip()
            expr = expr.strip().rstrip(";")
            if not name or not expr:
                continue
            hits.append((name, expr))
    return hits


def _load_goal(path):
    goals = []
    if not path:
        return goals
    with open(path, "r", encoding="utf-8", errors="ignore") as handle:
        for raw in handle:
            line = _strip_comments(raw)
            if not line:
                continue
            goals.append(line.rstrip(";"))
    return goals


def _make_safe_name(name):
    safe = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if not safe or safe[0].isdigit():
        safe = "hit_" + safe
    return safe


def _sanitize_sym(text):
    safe = re.sub(r"[^A-Za-z0-9_]", "_", text)
    if not safe or safe[0].isdigit():
        safe = "v_" + safe
    return safe


def _extract_sum_le_one_terms(expr):
    if pcc is not None:
        expr = pcc._strip_sv_comments(expr)
    expr = re.sub(r"@\s*\([^)]*\)", "", expr).strip()
    if "<=" not in expr:
        return []
    lhs, rhs = expr.split("<=", 1)
    rhs = rhs.strip().rstrip(";")
    if rhs not in {"1", "1'b1", "1'b01", "1'd1"}:
        return []
    lhs = lhs.strip()
    if lhs.startswith("(") and lhs.endswith(")"):
        lhs = lhs[1:-1].strip()
    if "+" not in lhs:
        return []
    terms = [t.strip() for t in lhs.split("+")]
    if len(terms) < 2:
        return []
    for term in terms:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_\\.]*", term):
            return []
    return terms


def _rewrite_reduction_concat(expr):
    def repl(match):
        op = match.group(1)
        inner = match.group(2)
        parts = [p.strip() for p in inner.split(",") if p.strip()]
        if not parts:
            return "0"
        return "(" + op.join(parts) + ")"

    return re.sub(r"([&|^])\s*\{([^}]*)\}", repl, expr)


def _assignment_kinds():
    if SyntaxKind is None:
        return set()
    kinds = set()
    for name in dir(SyntaxKind):
        if not name.endswith("AssignmentExpression"):
            continue
        if name == "AssignmentPatternExpression":
            continue
        kinds.add(getattr(SyntaxKind, name))
    return kinds


def _control_kinds():
    if SyntaxKind is None:
        return set()
    return {
        SyntaxKind.ConditionalStatement,
        SyntaxKind.CaseStatement,
        SyntaxKind.RandCaseStatement,
    }


_ASSIGN_EXPR_KINDS = _assignment_kinds()
_CONTROL_KINDS = _control_kinds()


def _iter_module_decls(root):
    stack = [root]
    while stack:
        node = stack.pop()
        if not isinstance(node, SyntaxNode):
            continue
        if node.kind == SyntaxKind.ModuleDeclaration:
            yield node
        for child in node:
            if isinstance(child, SyntaxNode):
                stack.append(child)


def _extract_lhs_names(node):
    names = []

    def walk(n):
        if not isinstance(n, SyntaxNode):
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
            if isinstance(child, SyntaxNode):
                walk(child)

    walk(node)
    seen = set()
    uniq = []
    for name in names:
        if name not in seen:
            seen.add(name)
            uniq.append(name)
    return uniq


def _lhs_keys(node):
    keys = _extract_lhs_names(node)
    try:
        text = str(node).strip()
    except Exception:
        text = ""
    if text:
        text = re.sub(r"\s+", "", text)
        if "[" in text and "]" in text and text not in keys:
            keys.insert(0, text)
    return keys


def _rhs_literal_value(node):
    if node is None:
        return None
    text = str(node).strip()
    text = text.replace("_", "")
    if text in {"0", "1"}:
        return int(text)
    match = re.match(r"(?i)^(\d+)?'([bdh])([0-9a-f]+)$", text)
    if not match:
        return None
    width_str, base, digits = match.groups()
    base = base.lower()
    if base == "b":
        value = int(digits, 2)
    elif base == "h":
        value = int(digits, 16)
    else:
        value = int(digits, 10)
    return value


def _collect_module_assign_value_coverage(module_node, source_manager):
    stmt_map = {}
    branch_map = {}

    def line_of(node):
        return source_manager.getLineNumber(node.sourceRange.start)

    def add_coverage(names, stmt_line, control_lines, value):
        for name in names:
            stmt_map.setdefault(name, {}).setdefault(value, set()).add(stmt_line)
            if control_lines:
                branch_map.setdefault(name, {}).setdefault(value, set()).update(control_lines)

    def visit(node, control_stack):
        if node.kind in _CONTROL_KINDS:
            control_stack.append(line_of(node))
            for child in node:
                if isinstance(child, SyntaxNode):
                    visit(child, control_stack)
            control_stack.pop()
            return

        if node.kind == SyntaxKind.ExpressionStatement:
            expr = node.expr
            if expr is not None and expr.kind in _ASSIGN_EXPR_KINDS:
                names = _lhs_keys(expr.left)
                value = _rhs_literal_value(expr.right)
                if names and value is not None:
                    add_coverage(names, line_of(node), control_stack, value)
            return

        if node.kind == SyntaxKind.ContinuousAssign:
            assigns = getattr(node, "assignments", None)
            if assigns is not None:
                for item in assigns:
                    if isinstance(item, SyntaxNode) and item.kind in _ASSIGN_EXPR_KINDS:
                        names = _lhs_keys(item.left)
                        value = _rhs_literal_value(item.right)
                        if names and value is not None:
                            add_coverage(names, line_of(item), control_stack, value)
            return

        for child in node:
            if isinstance(child, SyntaxNode):
                visit(child, control_stack)

    visit(module_node, [])
    return stmt_map, branch_map


def _build_value_coverage(verilog_files, include_dirs=None):
    if SyntaxTree is None:
        return None
    include_dirs = include_dirs or []
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
            stmt_map, branch_map = _collect_module_assign_value_coverage(module_node, sm)
            if module_name in module_cov:
                existing = module_cov[module_name]
                for var, vmap in stmt_map.items():
                    for val, lines in vmap.items():
                        existing["stmt"].setdefault(var, {}).setdefault(val, set()).update(lines)
                for var, vmap in branch_map.items():
                    for val, lines in vmap.items():
                        existing["branch"].setdefault(var, {}).setdefault(val, set()).update(lines)
            else:
                module_cov[module_name] = {
                    "file": path,
                    "stmt": stmt_map,
                    "branch": branch_map,
                }
    return module_cov


def _const_value(node):
    if sva is None or node is None:
        return None
    if isinstance(node, sva.BoolConst):
        return 1 if node.value else 0
    if isinstance(node, sva.NumConst):
        return node.value
    if isinstance(node, sva.BitVecConst):
        try:
            return int(node.bits, 2)
        except Exception:
            return None
    return None


def _atom_key_from_expr(node):
    if sva is None or node is None:
        return None
    if isinstance(node, sva.Identifier):
        return node.name
    if isinstance(node, sva.BitSelect):
        base = _atom_key_from_expr(node.var)
        if base is None:
            return None
        return f"{base}[{node.idx}]"
    if isinstance(node, sva.RangeSelect):
        base = _atom_key_from_expr(node.var)
        if base is None:
            return None
        return f"{base}[{node.left}:{node.right}]"
    return None


def _swap_range_key(key):
    if not key or ":" not in key or "[" not in key or "]" not in key:
        return None
    match = re.match(r"^(.*)\[(\d+):(\d+)\]$", key)
    if not match:
        return None
    base, left, right = match.groups()
    return f"{base}[{right}:{left}]"


def _collect_bool_exprs_from_seq(seq, out):
    if sva is None or seq is None:
        return
    if isinstance(seq, sva.SeqBool):
        out.append(seq.expr)
        return
    if isinstance(seq, sva.SeqDelay):
        _collect_bool_exprs_from_seq(seq.left, out)
        _collect_bool_exprs_from_seq(seq.right, out)
        return
    if isinstance(seq, sva.SeqRepeat):
        _collect_bool_exprs_from_seq(seq.seq, out)
        return
    if isinstance(seq, sva.SeqThroughout):
        out.append(seq.cond_expr)
        _collect_bool_exprs_from_seq(seq.seq, out)
        return


def _extract_atoms_from_sva(expr):
    if sva is None or pcc is None:
        return []
    stripped = sva._strip_assert_wrapper(expr)
    stripped, _ = sva._split_disable_iff(stripped)
    stripped = _rewrite_reduction_concat(stripped)
    stripped = re.sub(r"@\s*\([^)]*\)", "", stripped)
    try:
        tokens = sva.tokenize(stripped)
        parser = sva.Parser(tokens)
        prop = parser.parse_property()
    except Exception:
        # Fallback: very small regex-based extractor for simple combinational forms.
        cleaned = stripped
        cleaned = re.sub(r"@\s*\([^)]*\)", "", cleaned).strip()
        if "==" not in cleaned:
            return []
        lhs, rhs = cleaned.split("==", 1)
        lhs = lhs.strip().strip("()")
        rhs = rhs.strip().rstrip(";").strip("()")
        atoms = []
        ident_re = re.compile(r"[A-Za-z_][A-Za-z0-9_\\.]*")
        lhs_id = ident_re.findall(lhs)
        if lhs_id:
            atoms.append((lhs_id[0], 1))
        rhs_ids = []
        if "{ " in rhs or "{" in rhs:
            match = re.search(r"\{([^}]*)\}", rhs)
            if match:
                parts = [p.strip() for p in match.group(1).split(",") if p.strip()]
                rhs_ids.extend(parts)
        if not rhs_ids:
            rhs_ids = [p.strip() for p in rhs.replace("(", "").replace(")", "").split("|")]
        for ident in rhs_ids:
            match = ident_re.match(ident)
            if match:
                atoms.append((match.group(0), 1))
        seen = set()
        uniq = []
        for key, val in atoms:
            tag = (key, val)
            if tag in seen:
                continue
            seen.add(tag)
            uniq.append(tag)
        return uniq
    bool_exprs = []
    _collect_bool_exprs_from_seq(prop.antecedent, bool_exprs)
    if prop.consequent is not None:
        _collect_bool_exprs_from_seq(prop.consequent, bool_exprs)
    atoms = []

    def walk(node):
        if node is None:
            return
        if isinstance(node, sva.CompareOp):
            if node.op == "==":
                key = _atom_key_from_expr(node.left)
                val = _const_value(node.right)
                if key is None:
                    key = _atom_key_from_expr(node.right)
                    val = _const_value(node.left)
                if key is not None and val is not None:
                    atoms.append((key, val))
                    return
            walk(node.left)
            walk(node.right)
            return
        if isinstance(node, sva.BinaryOp):
            walk(node.left)
            walk(node.right)
            return
        if isinstance(node, sva.Not):
            walk(node.expr)
            return
        if isinstance(node, (sva.Identifier, sva.BitSelect, sva.RangeSelect)):
            key = _atom_key_from_expr(node)
            if key is not None:
                atoms.append((key, 1))
            return

    for bexpr in bool_exprs:
        walk(bexpr)
    # De-dup while preserving order
    seen = set()
    uniq = []
    for key, val in atoms:
        tag = (key, val)
        if tag in seen:
            continue
        seen.add(tag)
        uniq.append(tag)
    return uniq


def _minimize_cover(lines_by_signal):
    signals = {sig for sig, lines in lines_by_signal.items() if lines}
    if not signals:
        return set()
    all_lines = sorted({line for lines in lines_by_signal.values() for line in lines})
    var_map = {line: z3.Bool(_sanitize_sym(line)) for line in all_lines}
    opt = z3.Optimize()
    for sig in sorted(signals):
        opts = [var_map[line] for line in lines_by_signal.get(sig, set())]
        if opts:
            opt.add(z3.Or(opts))
    opt.minimize(z3.Sum([z3.If(var_map[line], 1, 0) for line in all_lines]))
    if opt.check() != z3.sat:
        return set()
    model = opt.model()
    chosen = {line for line, var in var_map.items() if z3.is_true(model.eval(var, model_completion=True))}
    return chosen


def _resolve_module_for_node(node, scope_module_map, top_module):
    scope, var = pcc._split_scope_name(node)
    module = top_module if not scope else scope_module_map.get(scope)
    if not module and scope:
        parts = scope.split(".")
        for idx in range(1, len(parts)):
            candidate = ".".join(parts[idx:])
            module = scope_module_map.get(candidate)
            if module:
                scope = candidate
                break
    return module, scope, var


def _find_module_for_var(var, module_cov):
    if not module_cov:
        return None
    base = var.split("[", 1)[0] if var else var
    matches = []
    for mod, entry in module_cov.items():
        stmt = entry.get("stmt", {})
        branch = entry.get("branch", {})
        if var in stmt or var in branch or base in stmt or base in branch:
            matches.append(mod)
    if len(matches) == 1:
        return matches[0]
    return None


def _cov_has_var(entry, var):
    if not entry or not var:
        return False
    base = var.split("[", 1)[0]
    stmt = entry.get("stmt", {})
    branch = entry.get("branch", {})
    return var in stmt or var in branch or base in stmt or base in branch


def _modules_for_var(var, module_cov):
    mods = set()
    if not module_cov or not var:
        return mods
    base = var.split("[", 1)[0]
    for mod, entry in module_cov.items():
        stmt = entry.get("stmt", {})
        branch = entry.get("branch", {})
        if var in stmt or var in branch or base in stmt or base in branch:
            mods.add(mod)
    return mods


def _find_common_module(vars_list, module_cov):
    candidates = None
    for var in vars_list:
        mods = _modules_for_var(var, module_cov)
        if not mods:
            return None
        candidates = mods if candidates is None else candidates & mods
        if not candidates:
            return None
    if candidates and len(candidates) == 1:
        return next(iter(candidates))
    return None


def _collect_allowed_lines(kept, slang_cov, module_files, scope_module_map, top_module):
    if not kept:
        return None, None
    allowed_stmt = set()
    allowed_branch = set()
    for node in kept:
        if not node:
            continue
        module, _, var = _resolve_module_for_node(node, scope_module_map, top_module)
        cov_entry = slang_cov.get(module) if module else None
        if not cov_entry or not _cov_has_var(cov_entry, var):
            module = _find_module_for_var(var, slang_cov)
            cov_entry = slang_cov.get(module) if module else None
        if not cov_entry:
            continue
        file_path = module_files.get(module) or cov_entry.get("file") or module
        keys = [var]
        swapped = _swap_range_key(var)
        if swapped and swapped not in keys:
            keys.append(swapped)
        if "[" in var:
            base = var.split("[", 1)[0]
            if base not in keys:
                keys.append(base)
        for k in keys:
            for line in cov_entry["stmt"].get(k, set()):
                allowed_stmt.add(f"{file_path}:{line}")
            for line in cov_entry["branch"].get(k, set()):
                allowed_branch.add(f"{file_path}:{line}")
    return allowed_stmt, allowed_branch


def _filter_assumptions_for_label(entries, label):
    if not entries:
        return []
    has_labels = any(lbl is not None for lbl, _ in entries)
    if not has_labels:
        return [expr for _, expr in entries]
    selected = []
    for lbl, expr in entries:
        if lbl is None:
            continue
        if lbl == "*":
            selected.append(expr)
            continue
        if lbl == label or (label and label.startswith(lbl + "__inst")):
            selected.append(expr)
            continue
        if label and lbl.startswith(label + "__inst"):
            selected.append(expr)
    return selected


def _core_mode(args):
    if pcc is None or extract_coi is None or build_slang_coverage is None:
        print("Missing dependencies for core mode.", file=sys.stderr)
        return 2

    vfiles = list(dict.fromkeys(args.verilog_files))
    if not vfiles:
        print("No Verilog files provided.", file=sys.stderr)
        return 2

    expressions = pcc._extract_assertion_expressions_from_file(args.assertion_file)
    labels = None
    if args.rewrite_module_prefixes:
        module_to_scopes = pcc._build_module_instance_map(
            vfiles, args.top, args.include, args.clock
        )
        expressions, labels = pcc._rewrite_expressions_with_instance_scopes(
            expressions, module_to_scopes, max_expansions=args.max_expansions
        )
    if labels is None:
        labels = [f"assertion_{idx + 1}" for idx in range(len(expressions))]

    if args.assertion_label:
        if args.assertion_label not in labels:
            print("Assertion label not found: %s" % args.assertion_label, file=sys.stderr)
            return 2
        sel_idx = labels.index(args.assertion_label)
    else:
        sel_idx = max(args.assertion_index - 1, 0)
        if sel_idx >= len(expressions):
            print("Assertion index out of range.", file=sys.stderr)
            return 2

    expr = expressions[sel_idx]
    label = labels[sel_idx]

    assumption_entries = []
    for path in args.assume_file or []:
        assumption_entries.extend(pcc._extract_assumption_expressions_from_file(path))
    assumption_exprs = _filter_assumptions_for_label(assumption_entries, label)

    targets = pcc._extract_targets_from_expression(expr)
    status, kept, _, _ = pcc.run_cegar(
        vfiles,
        top_module=args.top,
        assertion_expr=expr,
        targets=targets,
        include_dirs=args.include,
        clocks=args.clock,
        a1_depth=None,
        a1_max_state=None,
        max_iter=None,
        use_sva2smt=False,
        sva2smt_bin=None,
        sva_max_time=args.sva_max_time,
        assumption_exprs=assumption_exprs,
    )
    if status != "proved" or kept is None:
        print("Assertion %s not proved (status=%s)" % (label, status), file=sys.stderr)
        return 1

    result = extract_coi(
        vfiles,
        top_module=args.top,
        include_dirs=args.include,
        clocks=args.clock,
        temporal_depth=1,
        strip_assertions=True,
    )
    scope_module_map = result["scope_module_map"]
    module_files = pcc._map_module_files(vfiles)
    slang_cov = build_slang_coverage(list(module_files.values()), include_dirs=args.include)
    if slang_cov is None:
        print("slang coverage unavailable; cannot refine.", file=sys.stderr)
        return 1
    value_cov = _build_value_coverage(list(module_files.values()), include_dirs=args.include)
    allowed_stmt, allowed_branch = _collect_allowed_lines(
        kept, slang_cov, module_files, scope_module_map, args.top
    )

    terms = _extract_sum_le_one_terms(expr)
    atoms = _extract_atoms_from_sva(expr) if not terms else []
    target_nodes = terms if terms else kept

    stmt_lines_by_sig = {}
    branch_lines_by_sig = {}
    for node in target_nodes:
        module, _, var = _resolve_module_for_node(node, scope_module_map, args.top)
        if not module:
            continue
        cov_entry = slang_cov.get(module)
        if not cov_entry:
            continue
        file_path = module_files.get(module) or cov_entry.get("file") or module
        stmt_lines = set()
        branch_lines = set()
        if terms and value_cov and module in value_cov:
            ventry = value_cov[module]
            stmt_lines = ventry["stmt"].get(var, {}).get(1, set())
            branch_lines = ventry["branch"].get(var, {}).get(1, set())
        if not stmt_lines:
            stmt_lines = cov_entry["stmt"].get(var, set())
        if not branch_lines:
            branch_lines = cov_entry["branch"].get(var, set())
        if stmt_lines:
            lines = {f"{file_path}:{line}" for line in stmt_lines}
            if allowed_stmt is not None:
                lines = lines & allowed_stmt
            if lines:
                stmt_lines_by_sig.setdefault(node, set()).update(lines)
        if branch_lines:
            lines = {f"{file_path}:{line}" for line in branch_lines}
            if allowed_branch is not None:
                lines = lines & allowed_branch
            if lines:
                branch_lines_by_sig.setdefault(node, set()).update(lines)

    if atoms:
        stmt_lines_by_sig = {}
        branch_lines_by_sig = {}
        unscoped_vars = []
        for key, _ in atoms:
            scope, var = pcc._split_scope_name(key)
            if not scope:
                unscoped_vars.append(var)
        common_module = _find_common_module(unscoped_vars, slang_cov) if unscoped_vars else None
        for key, val in atoms:
            module, _, var = _resolve_module_for_node(key, scope_module_map, args.top)
            cov_entry = slang_cov.get(module) if module else None
            if not cov_entry or not _cov_has_var(cov_entry, var):
                module = _find_module_for_var(var, slang_cov)
                cov_entry = slang_cov.get(module) if module else None
            if (not cov_entry or not _cov_has_var(cov_entry, var)) and common_module:
                module = common_module
                cov_entry = slang_cov.get(module) if module else None
            if not cov_entry:
                continue
            file_path = module_files.get(module) or cov_entry.get("file") or module
            stmt_lines = set()
            branch_lines = set()
            keys = [var]
            swapped = _swap_range_key(var)
            if swapped and swapped not in keys:
                keys.append(swapped)
            if "[" in var:
                base = var.split("[", 1)[0]
                if base not in keys:
                    keys.append(base)
            if value_cov and module in value_cov:
                ventry = value_cov[module]
                for k in keys:
                    stmt_lines = ventry["stmt"].get(k, {}).get(val, set())
                    if stmt_lines:
                        break
                for k in keys:
                    branch_lines = ventry["branch"].get(k, {}).get(val, set())
                    if branch_lines:
                        break
            if not stmt_lines:
                for k in keys:
                    stmt_lines = cov_entry["stmt"].get(k, set())
                    if stmt_lines:
                        break
            if not branch_lines:
                for k in keys:
                    branch_lines = cov_entry["branch"].get(k, set())
                    if branch_lines:
                        break
            if stmt_lines:
                lines = {f"{file_path}:{line}" for line in stmt_lines}
                if allowed_stmt is not None:
                    lines = lines & allowed_stmt
                if lines:
                    stmt_lines_by_sig.setdefault(f"{key}=={val}", set()).update(lines)
            if branch_lines:
                lines = {f"{file_path}:{line}" for line in branch_lines}
                if allowed_branch is not None:
                    lines = lines & allowed_branch
                if lines:
                    branch_lines_by_sig.setdefault(f"{key}=={val}", set()).update(lines)

    stmt_min = _minimize_cover(stmt_lines_by_sig)
    branch_min = _minimize_cover(branch_lines_by_sig)

    print("Assertion %s minimal statements %d" % (label, len(stmt_min)))
    for loc in sorted(stmt_min):
        print("S %s %s" % (label, loc))
    print("Assertion %s minimal branches %d" % (label, len(branch_min)))
    for loc in sorted(branch_min):
        print("B %s %s" % (label, loc))
    return 0


def main():
    parser = argparse.ArgumentParser(
        description="MaxSAT-based coverage refiner (prototype)."
    )
    parser.add_argument("--base-smt2", help="Base SMT2 with design+property")
    parser.add_argument("--hits", help="Hit definitions: name: <smt2-bool-expr>")
    parser.add_argument("--goal", help="Optional file with extra hard assertions")
    parser.add_argument(
        "--require-any",
        action="store_true",
        help="Require at least one hit to be true",
    )
    parser.add_argument(
        "--dump-smt2",
        help="Write the combined SMT2 to this path for inspection",
    )
    parser.add_argument("--top", help="Top module (core refine mode)")
    parser.add_argument("--assertion-file", help="Assertion file (core refine mode)")
    parser.add_argument("--assertion-index", type=int, default=1, help="1-based index")
    parser.add_argument("--assertion-label", help="Assertion label to select")
    parser.add_argument("--assume-file", action="append", default=[], help="Assume file(s)")
    parser.add_argument("-I", "--include", action="append", default=[], help="Include dirs")
    parser.add_argument("-c", "--clock", default="DEFAULT_CLOCK:1", help="Clock spec")
    parser.add_argument("--rewrite-module-prefixes", action="store_true")
    parser.add_argument("--max-expansions", type=int, default=256)
    parser.add_argument("--sva-max-time", type=int, default=10)
    parser.add_argument("verilog_files", nargs="*")
    args = parser.parse_args()

    if args.base_smt2:
        base_text = open(args.base_smt2, "r", encoding="utf-8", errors="ignore").read()
        base_text = _strip_commands(base_text)

        hits = _load_hits(args.hits)
        if not hits:
            print("No hits found.", file=sys.stderr)
            return 2

        goals = _load_goal(args.goal)

        smt_lines = [base_text]
        hit_vars = []
        name_map = {}
        for name, expr in hits:
            safe = _make_safe_name(name)
            while safe in name_map.values():
                safe = "_" + safe
            name_map[name] = safe
            hit_vars.append(safe)
            smt_lines.append(f"(declare-const {safe} Bool)")
            smt_lines.append(f"(assert (= {safe} {expr}))")
            smt_lines.append(f"(assert-soft (not {safe}) :weight 1)")

        for expr in goals:
            smt_lines.append(f"(assert {expr})")

        if args.require_any:
            smt_lines.append("(assert (or %s))" % " ".join(hit_vars))

        combined = "\n".join(smt_lines)
        if args.dump_smt2:
            with open(args.dump_smt2, "w", encoding="utf-8") as handle:
                handle.write(combined)

        opt = z3.Optimize()
        opt.from_string(combined)
        if opt.check() != z3.sat:
            print("UNSAT (no witness under current goals).", file=sys.stderr)
            return 1

        model = opt.model()
        chosen = []
        for orig, safe in name_map.items():
            val = model.eval(z3.Bool(safe), model_completion=True)
            if z3.is_true(val):
                chosen.append(orig)

        print("Minimized hits: %d / %d" % (len(chosen), len(hits)))
        for name in sorted(chosen):
            print(name)
        return 0

    if not args.assertion_file or not args.top:
        print("Need either --base-smt2 or core mode args.", file=sys.stderr)
        return 2
    return _core_mode(args)


if __name__ == "__main__":
    raise SystemExit(main())
