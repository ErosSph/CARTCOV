#!/usr/bin/env python3
import argparse
import logging
import os
import re
import subprocess
import sys
import tempfile
from contextlib import redirect_stdout
import io

import z3

from sva_to_smt import (
    Context,
    Parser,
    ParseError,
    _cast_to_bool,
    tokenize,
    translate_sva_property,
)

from static_analysis import expressions
from static_coi_extractor import (
    SV_KEYWORDS,
    build_elaborate_info,
    collect_state_vars,
    compute_a1_for_targets,
    extract_assertion_targets,
    extract_coi,
)
from static_analysis import Linking
from slang_coverage import build_coverage as build_slang_coverage

LOG = logging.getLogger("proof_core_cegar")
QUIET_OUTPUT = False


def _setup_logger(log_file):
    LOG.handlers.clear()
    LOG.setLevel(logging.INFO)
    handler = logging.FileHandler(log_file, mode="w", encoding="utf-8")
    handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    LOG.addHandler(handler)
    return LOG


def _write_text(path, content):
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(content)


def _strip_sv_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.DOTALL)
    text = re.sub(r"//.*", " ", text)
    return text


def _rewrite_sum_le_one(expr):
    expr = expr.strip().rstrip(";")
    if "<=" not in expr:
        return None
    lhs, rhs = expr.split("<=", 1)
    rhs = rhs.strip()
    if rhs not in {"1", "1'b1", "1'b01", "1'd1"}:
        return None
    lhs = lhs.strip()
    if lhs.startswith("(") and lhs.endswith(")"):
        lhs = lhs[1:-1].strip()
    if "+" not in lhs:
        return None
    terms = [t.strip() for t in lhs.split("+")]
    if len(terms) < 2:
        return None
    for t in terms:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_\\.]*", t):
            return None
    pairs = []
    for i in range(len(terms)):
        for j in range(i + 1, len(terms)):
            pairs.append(f"!({terms[i]}&{terms[j]})")
    return "&".join(pairs) if pairs else None


def _rewrite_reduction_concat(expr):
    def repl(match):
        op = match.group(1)
        inner = match.group(2)
        parts = [p.strip() for p in inner.split(",") if p.strip()]
        if not parts:
            return "0"
        return "(" + op.join(parts) + ")"

    return re.sub(r"([&|^])\s*\{([^}]*)\}", repl, expr)


def _rewrite_disable_iff(expr):
    match = re.match(r"(?s)\s*disable\s+iff\s*\(([^)]*)\)\s*(.*)", expr)
    if not match:
        return expr
    cond = match.group(1).strip()
    body = match.group(2).strip()
    if not cond or not body:
        return expr
    return f"(!({cond})) | ({body})"


def _parse_sv_int_literal(token):
    match = re.match(r"(?i)^(\d+)?'([bdh])([0-9a-f_xz]+)$", token)
    if not match:
        return None
    width_str, base, digits = match.groups()
    digits = digits.replace("_", "")
    if re.search(r"[xz]", digits, flags=re.IGNORECASE):
        return None
    base = base.lower()
    if base == "b":
        value = int(digits, 2)
    elif base == "h":
        value = int(digits, 16)
    else:
        value = int(digits, 10)
    width = int(width_str) if width_str else None
    return value, width


def _parse_sv_const_expr(expr, const_map):
    expr = expr.strip()
    if expr.startswith("(") and expr.endswith(")"):
        expr = expr[1:-1].strip()
    parsed = _parse_sv_int_literal(expr)
    if parsed is not None:
        return parsed
    if re.fullmatch(r"\d+", expr):
        return int(expr), None
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", expr):
        return const_map.get(expr)
    return None


def _extract_param_constants(verilog_files):
    const_map = {}
    param_block = re.compile(r"\b(localparam|parameter)\b([^;]*);", flags=re.DOTALL)
    for vfile in verilog_files:
        try:
            text = open(vfile, "r", encoding="utf-8", errors="ignore").read()
        except OSError:
            continue
        stripped = _strip_sv_comments(text)
        for match in param_block.finditer(stripped):
            body = match.group(2)
            body = re.sub(r"\[[^\]]+\]", " ", body)
            body = re.sub(
                r"\b(?:signed|unsigned|integer|logic|reg|wire|bit)\b", " ", body
            )
            for assign in re.finditer(
                r"([A-Za-z_][A-Za-z0-9_$]*)\s*=\s*([^,]+)", body
            ):
                name = assign.group(1)
                value_expr = assign.group(2).strip()
                parsed = _parse_sv_const_expr(value_expr, const_map)
                if parsed is not None:
                    const_map[name] = parsed
    return const_map


def _strip_initial_blocks(text):
    lines = text.splitlines(True)
    out_lines = []
    in_initial = False
    depth = 0
    for line in lines:
        if not in_initial:
            if re.search(r"\binitial\b", line):
                if re.search(r"\bbegin\b", line):
                    in_initial = True
                    depth = 0
                    depth += len(re.findall(r"\bbegin\b", line))
                    depth -= len(re.findall(r"\bend\b", line))
                    if depth <= 0:
                        in_initial = False
                    continue
                if ";" in line:
                    continue
                in_initial = True
                depth = 0
                continue
            out_lines.append(line)
        else:
            depth += len(re.findall(r"\bbegin\b", line))
            depth -= len(re.findall(r"\bend\b", line))
            if depth <= 0 and re.search(r"\bend\b", line):
                in_initial = False
            continue
    return "".join(out_lines)


def _emit_coverage_only(label, coverage):
    stmt_cov, branch_cov = coverage
    for loc in sorted(stmt_cov):
        print(f"S {label} {loc}")
    for loc in sorted(branch_cov):
        print(f"B {label} {loc}")


def _extract_targets_from_expression(expr):
    expr = re.sub(r"@\s*\([^)]*\)", " ", expr)
    expr = re.sub(r"\d+'[bdh][0-9a-fA-F_xXzZ]+", " ", expr)
    expr = re.sub(r"\b\d+\b", " ", expr)
    expr = re.sub(r"\$[A-Za-z_][A-Za-z0-9_]*", " ", expr)
    tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_\\.]*", expr)
    targets = [tok for tok in tokens if tok not in SV_KEYWORDS]
    return list(dict.fromkeys(targets))


def _build_assertion_groups_from_expressions(expressions, labels=None):
    labeled = []
    for idx, expr in enumerate(expressions):
        label = labels[idx] if labels else "assertion_%d" % (idx + 1)
        targets = _extract_targets_from_expression(expr)
        labeled.append((label, targets))
    return labeled


def _build_module_instance_map(vfiles, top_module, include_dirs, clocks):
    elaborate_info, _, _ = build_elaborate_info(
        vfiles, include_dirs=include_dirs, clocks=clocks
    )
    with redirect_stdout(io.StringIO()):
        _, _, scope_module_map = Linking(elaborate_info, top_module)
    module_to_scopes = {top_module: [""]}
    for scope, module in scope_module_map.items():
        module_to_scopes.setdefault(module, []).append(scope)
    return module_to_scopes


def _rewrite_expressions_with_instance_scopes(
    expressions, module_to_scopes, max_expansions=256
):
    new_exprs = []
    new_labels = []
    for idx, expr in enumerate(expressions):
        expansions = [expr]
        for module_name, scopes in module_to_scopes.items():
            pattern = re.compile(r"(?<![A-Za-z0-9_$])" + re.escape(module_name) + r"\.")
            if not any(pattern.search(e) for e in expansions):
                continue
            replacements = [s + "." if s else "" for s in scopes]
            next_expansions = []
            for e in expansions:
                if not pattern.search(e):
                    next_expansions.append(e)
                    continue
                for rep in replacements:
                    next_expansions.append(pattern.sub(rep, e))
            expansions = next_expansions
            if len(expansions) > max_expansions:
                raise ValueError(
                    "Assertion %d expanded to %d variants (limit %d). "
                    "Reduce instances or increase --max-expansions."
                    % (idx + 1, len(expansions), max_expansions)
                )
        for jdx, e in enumerate(expansions):
            if len(expansions) == 1:
                label = "assertion_%d" % (idx + 1)
            else:
                label = "assertion_%d__inst%d" % (idx + 1, jdx + 1)
            new_exprs.append(e)
            new_labels.append(label)
    return new_exprs, new_labels


def _map_module_files(verilog_files):
    module_files = {}
    pattern = re.compile(r"\bmodule\s+([A-Za-z_][A-Za-z0-9_$]*)")
    for vfile in verilog_files:
        try:
            text = open(vfile, "r", encoding="utf-8", errors="ignore").read()
        except OSError:
            continue
        stripped = _strip_sv_comments(text)
        for match in pattern.finditer(stripped):
            module = match.group(1)
            module_files.setdefault(module, vfile)
    return module_files


def _scan_module_decl_lines(module_files):
    pattern = re.compile(r"\bmodule\s+([A-Za-z_][A-Za-z0-9_$]*)")
    module_src_lines = {}
    for vfile in set(module_files.values()):
        try:
            with open(vfile, "r", encoding="utf-8", errors="ignore") as handle:
                for lineno, line in enumerate(handle, 1):
                    m = pattern.search(line)
                    if m:
                        name = m.group(1)
                        module_src_lines.setdefault(name, lineno)
        except OSError:
            continue
    return module_src_lines


def _compute_module_line_offsets(elaborate_info, module_files):
    module_src_lines = _scan_module_decl_lines(module_files)
    offsets = {}
    for name, info in elaborate_info.items():
        src_line = module_src_lines.get(name)
        ast_line = info.get("module_lineno")
        if src_line and ast_line:
            offsets[name] = ast_line - src_line
    return offsets


def _split_scope_name(node):
    if "." in node:
        scope, var = node.rsplit(".", 1)
        return scope, var
    return "", node


def _collect_proof_core_coverage(
    kept_nodes,
    elaborate_info,
    top_module,
    scope_module_map,
    module_files,
    module_line_offsets=None,
    include_dirs=None,
):
    statements = set()
    branches = set()
    module_line_offsets = module_line_offsets or {}
    slang_cov = None
    try:
        slang_cov = build_slang_coverage(
            list(module_files.values()), include_dirs=include_dirs
        )
    except Exception as err:
        LOG.warning("slang coverage failed (%s), falling back to pyverilog mapping", err)
        slang_cov = None
    for node in kept_nodes:
        if not node:
            continue
        scope, var = _split_scope_name(node)
        module = top_module if not scope else scope_module_map.get(scope)
        if not module and scope:
            parts = scope.split(".")
            for idx in range(1, len(parts)):
                candidate = ".".join(parts[idx:])
                module = scope_module_map.get(candidate)
                if module:
                    scope = candidate
                    break
        if not module:
            continue
        if slang_cov and module in slang_cov:
            cov_entry = slang_cov[module]
            file_path = module_files.get(module) or cov_entry.get("file")
            stmt_lines = cov_entry["stmt"].get(var, set())
            branch_lines = cov_entry["branch"].get(var, set())
            for line_no in stmt_lines:
                loc = f"{file_path}:{line_no}" if file_path else f"{module}:{line_no}"
                statements.add(loc)
            for line_no in branch_lines:
                loc = f"{file_path}:{line_no}" if file_path else f"{module}:{line_no}"
                branches.add(loc)
            continue
        expr_map = expressions(["", scope, var], top_module, scope_module_map, elaborate_info)
        for line_key in expr_map:
            if not line_key:
                continue
            line = line_key
            kind = None
            if isinstance(line_key, str) and ":" in line_key:
                line_part, suffix = line_key.split(":", 1)
                line = line_part
                if suffix == "D":
                    kind = "D"
                elif suffix == "C":
                    kind = "C"
            try:
                line_no = int(line)
            except (TypeError, ValueError):
                continue
            offset = module_line_offsets.get(module, 0)
            if offset:
                line_no -= offset
                if line_no <= 0:
                    continue
            file_path = module_files.get(module)
            loc = f"{file_path}:{line_no}" if file_path else f"{module}:{line_no}"
            if kind == "C":
                branches.add(loc)
            else:
                statements.add(loc)
    return statements, branches


def _extract_assertion_expressions_from_text(text):
    expressions = []
    stripped = _strip_sv_comments(text)
    assert_re = re.compile(r"\bassert\b")
    idx = 0
    while True:
        match = assert_re.search(stripped, idx)
        if not match:
            break
        pos = match.start()
        tail = stripped[pos:]
        paren_idx = tail.find("(")
        if paren_idx != -1:
            depth = 0
            start = None
            for jdx in range(paren_idx, len(tail)):
                if tail[jdx] == "(":
                    if depth == 0:
                        start = jdx + 1
                    depth += 1
                elif tail[jdx] == ")":
                    depth -= 1
                    if depth == 0 and start is not None:
                        expressions.append(tail[start:jdx])
                        idx = pos + jdx + 1
                        break
            else:
                idx = pos + len("assert")
        else:
            idx = pos + len("assert")
    return expressions


def _extract_assertion_expressions_from_file(path):
    with open(path, "r", encoding="utf-8", errors="ignore") as handle:
        text = handle.read()
    expressions = _extract_assertion_expressions_from_text(text)
    if expressions:
        return expressions
    # Fallback: treat each non-comment line as a raw expression.
    fallback = []
    for line in text.splitlines():
        raw = line.strip()
        if not raw:
            continue
        if raw.startswith("#") or raw.startswith("//") or raw.startswith("-"):
            continue
        if ":" in raw:
            _, raw = raw.split(":", 1)
        raw = raw.strip().rstrip(";")
        if raw:
            fallback.append(raw)
    return fallback


def _extract_assumption_expressions_from_file(path):
    with open(path, "r", encoding="utf-8", errors="ignore") as handle:
        text = handle.read()
    expressions = _extract_assertion_expressions_from_text(text)
    if expressions:
        return [(None, expr) for expr in expressions]
    entries = []
    label_re = re.compile(r"^(\*|assertion_[A-Za-z0-9_]+)\s*:\s*(.+)$")
    for line in text.splitlines():
        raw = line.strip()
        if not raw:
            continue
        if raw.startswith("#") or raw.startswith("//") or raw.startswith("-"):
            continue
        raw = raw.strip().rstrip(";")
        if not raw:
            continue
        match = label_re.match(raw)
        if match:
            label = match.group(1)
            expr = match.group(2).strip()
            if expr:
                entries.append((label, expr))
            continue
        entries.append((None, raw))
    return entries


def _normalize_assumption_expr(expr):
    expr = _strip_sv_comments(expr)
    expr = re.sub(r"@\s*\([^)]*\)", "", expr).strip()
    if not expr:
        return None
    if re.search(r"\|->|\|=>|##|\bthroughout\b|\$", expr):
        return None
    expr = expr.replace("&&", "&").replace("||", "|")
    rewritten = _rewrite_sum_le_one(expr)
    if rewritten:
        return rewritten
    return expr


def _signal_widths_from_types(signal_types):
    widths = {}
    for name, typ in (signal_types or {}).items():
        if not typ:
            continue
        widths[name] = typ[1] if typ[0] == "BitVec" else 1
    return widths


def _emit_assumptions(
    lines,
    assumptions,
    signal_map,
    signal_types,
    const_map,
    signal_widths,
    states,
):
    if not assumptions:
        return
    alias_cache = {}
    ctx = None
    if any(kind == "sva" for kind, _ in assumptions):
        if signal_widths is None:
            signal_widths = _signal_widths_from_types(signal_types)
        ctx = Context(signal_map, signal_widths, len(states) - 1)
    for idx, state in enumerate(states):
        for kind, expr in assumptions:
            if kind == "simple":
                smt_expr = _ast_to_smt2(
                    expr,
                    signal_map,
                    state,
                    alias_cache,
                    const_map,
                    signal_types,
                    ("Bool", 1),
                )
            else:
                smt_expr, typ = expr.to_smt(idx, ctx)
                if smt_expr is None:
                    continue
                smt_expr = _cast_to_bool(smt_expr, typ)
            lines.append("(assert %s)" % smt_expr)


def _rewrite_tokens_with_aliases(tokens, signal_map):
    for tok in tokens:
        if tok.kind != "IDENT":
            continue
        if tok.value in signal_map:
            continue
        resolved = _resolve_signal_alias(tok.value, signal_map, {})
        if resolved:
            tok.value = resolved


def _strip_assertions_from_verilog(text):
    text = _strip_sv_comments(text)
    text = re.sub(r"\bproperty\b.*?\bendproperty\b\s*;?", " ", text, flags=re.DOTALL)
    text = re.sub(r"\bassert\s+property\b.*?;", " ", text, flags=re.DOTALL)
    text = re.sub(r"(?m)^\s*assert\b.*?;", " ", text)
    text = re.sub(r"`assert\b[^;]*;", ";", text)
    text = _strip_initial_blocks(text)
    text = re.sub(r"\balways\b\s*#\s*[^;]*;", " ", text)
    return text


def _inject_keep_attributes(text, keep_names):
    if not keep_names:
        return text
    keep_set = set(keep_names)
    out_lines = []
    for line in text.splitlines(True):
        if "(*" in line:
            out_lines.append(line)
            continue
        stripped = line.lstrip()
        if not (
            stripped.startswith("wire")
            or stripped.startswith("reg")
            or stripped.startswith("logic")
        ):
            out_lines.append(line)
            continue
        if any(re.search(r"\b%s\b" % re.escape(name), line) for name in keep_set):
            indent = line[: len(line) - len(stripped)]
            out_lines.append("%s(* keep *) %s" % (indent, stripped))
        else:
            out_lines.append(line)
    return "".join(out_lines)


def _prepare_verilog_files(verilog_files, keep_signals=None):
    temp_dir = tempfile.mkdtemp(prefix="proof_core_strip_")
    stripped_files = []
    for vfile in verilog_files:
        with open(vfile, "r") as handle:
            stripped = _strip_assertions_from_verilog(handle.read())
        if keep_signals:
            stripped = _inject_keep_attributes(stripped, keep_signals)
        out_path = os.path.join(temp_dir, os.path.basename(vfile))
        with open(out_path, "w") as handle:
            handle.write(stripped)
        stripped_files.append(out_path)
    return stripped_files


def _derive_keep_signals(assertion_expr, targets):
    keep = []
    expr_targets = _extract_targets_from_expression(assertion_expr)
    for name in expr_targets + list(targets or []):
        if not name:
            continue
        leaf = name.split(".")[-1]
        if leaf and leaf not in SV_KEYWORDS:
            keep.append(leaf)
    return list(dict.fromkeys(keep))


def _run_yosys_smt2(verilog_files, top_module, output_path, include_dirs=None, flatten=False):
    includes = ""
    if include_dirs:
        includes = " ".join("-I %s" % inc for inc in include_dirs)
    flatten_cmd = "flatten; " if flatten else ""
    cmd = (
        "read_verilog -sv {includes} {files}; "
        "prep -top {top}; "
        "{flatten}"
        "async2sync; dffunmap; "
        "write_smt2 -wires {out}"
    ).format(
        includes=includes,
        files=" ".join(verilog_files),
        top=top_module,
        flatten=flatten_cmd,
        out=output_path,
    )
    if QUIET_OUTPUT:
        subprocess.run(
            ["yosys", "-p", cmd],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    else:
        subprocess.run(["yosys", "-p", cmd], check=True)
    LOG.info("Generated SMT2: %s", output_path)


def _find_topmod(smt2_text):
    for line in smt2_text.splitlines():
        if line.startswith("; yosys-smt2-topmod"):
            return line.split()[-1]
    return None


def _extract_signal_map(smt2_text, top_module):
    signal_map = {}
    pattern = re.compile(r"\(define-fun \|%s_n ([^|]+)\|" % re.escape(top_module))
    for line in smt2_text.splitlines():
        match = pattern.search(line)
        if match:
            sig = match.group(1)
            signal_map[sig] = "|%s_n %s|" % (top_module, sig)
    return signal_map


def _extract_signal_types(smt2_text, top_module):
    type_map = {}
    pattern = re.compile(
        r"\(define-fun \|%s_n ([^|]+)\|\s+\(\(state \|%s_s\|\)\)\s+(Bool|\(_ BitVec \d+\))"
        % (re.escape(top_module), re.escape(top_module))
    )
    for line in smt2_text.splitlines():
        match = pattern.search(line)
        if not match:
            continue
        sig = match.group(1)
        type_str = match.group(2)
        if type_str == "Bool":
            type_map[sig] = ("Bool", 1)
            continue
        width_match = re.match(r"\(_ BitVec (\d+)\)", type_str)
        if width_match:
            type_map[sig] = ("BitVec", int(width_match.group(1)))
    return type_map


def _resolve_signal_alias(name, signal_map, cache):
    if name in cache:
        return cache[name]
    if name in signal_map:
        cache[name] = name
        return name
    candidates = [key for key in signal_map if key.endswith("." + name)]
    if len(candidates) == 1:
        cache[name] = candidates[0]
        return candidates[0]
    if candidates:
        min_depth = min(key.count(".") for key in candidates)
        best = [key for key in candidates if key.count(".") == min_depth]
        if len(best) == 1:
            cache[name] = best[0]
            return best[0]
    cache[name] = None
    return None


def _rewrite_transition(smt2_text, top_module, kept_regs):
    lines = smt2_text.splitlines()
    new_lines = []
    in_t = False
    t_lines = []
    t_header = ""
    t_footer = ""
    for line in lines:
        if line.startswith("(define-fun |%s_t|" % top_module):
            in_t = True
            t_header = line
            t_lines = []
            continue
        if in_t:
            if line.strip().endswith(") ; end of module %s" % top_module):
                t_footer = line
                in_t = False
                kept_lines = []
                for tline in t_lines:
                    if ";" in tline and "\\" in tline:
                        reg = tline.split("\\")[-1].strip()
                        if reg in kept_regs:
                            kept_lines.append(tline)
                    else:
                        kept_lines.append(tline)
                if not kept_lines:
                    new_lines.append(
                        "(define-fun |%s_t| ((state |%s_s|) (next_state |%s_s|)) Bool true)"
                        % (top_module, top_module, top_module)
                    )
                else:
                    new_lines.append(t_header)
                    new_lines.extend(kept_lines)
                    new_lines.append(t_footer)
                continue
            t_lines.append(line)
            continue
        new_lines.append(line)
    return "\n".join(new_lines)


def _parse_property(expr):
    expr = _strip_sv_comments(expr)
    expr = re.sub(r"@\s*\([^)]*\)", "", expr).strip()
    expr = _rewrite_disable_iff(expr)
    expr = _rewrite_reduction_concat(expr)
    if "|->" in expr:
        op = "|->"
    elif "|=>" in expr:
        op = "|=>"
    else:
        rewritten = _rewrite_sum_le_one(expr)
        if rewritten:
            return "1'b1", rewritten, 0
        return "1'b1", expr, 0
    antecedent, consequent = expr.split(op, 1)
    antecedent = antecedent.strip()
    consequent = consequent.strip()
    delay = 0
    match = re.match(r"##\s*(\d+)\s*(.*)", consequent)
    if match:
        delay = int(match.group(1))
        consequent = match.group(2).strip()
    if op == "|=>":
        delay += 1
    return antecedent, consequent, delay


def _should_use_sva_parser(expr):
    expr = _strip_sv_comments(expr)
    if re.search(r"\bassert\s+property\b", expr):
        return True
    if re.search(r"\bdisable\s+iff\b", expr):
        return True
    if "##" in expr or "throughout" in expr or "$" in expr:
        return True
    if "&&" in expr or "||" in expr:
        return True
    if "{" in expr or "}" in expr:
        return True
    if re.search(r"\[\s*\*\s*", expr):
        return True
    return False


def _needs_flatten(expr):
    expr = _strip_sv_comments(expr)
    return bool(re.search(r"[A-Za-z_][A-Za-z0-9_]*\.", expr))


def _tokenize_expr(expr):
    expr = expr.replace(" ", "")
    tokens = []
    idx = 0
    while idx < len(expr):
        if expr[idx].isdigit():
            start = idx
            while idx < len(expr) and (expr[idx].isdigit() or expr[idx] in "'bBhHxXzZ_"):
                idx += 1
            tokens.append(expr[start:idx])
            continue
        if expr[idx].isalnum() or expr[idx] in "_.":
            start = idx
            while idx < len(expr) and (expr[idx].isalnum() or expr[idx] in "_."):
                idx += 1
            tokens.append(expr[start:idx])
            continue
        if expr[idx] in "()!&|^":
            tokens.append(expr[idx])
            idx += 1
            continue
        if expr[idx] == "=" and idx + 1 < len(expr) and expr[idx + 1] == "=":
            tokens.append("==")
            idx += 2
            continue
        if expr[idx] == "!" and idx + 1 < len(expr) and expr[idx + 1] == "=":
            tokens.append("!=")
            idx += 2
            continue
        raise ValueError("Unexpected token in expression: %s" % expr[idx:])
    return tokens


def _parse_expr(tokens):
    def parse_primary(pos):
        if tokens[pos] == "(":
            node, pos = parse_expr(pos + 1)
            if tokens[pos] != ")":
                raise ValueError("Missing closing parenthesis")
            return node, pos + 1
        if tokens[pos] == "!":
            node, pos = parse_primary(pos + 1)
            return ("not", node), pos
        return tokens[pos], pos + 1

    def parse_and(pos):
        left, pos = parse_primary(pos)
        while pos < len(tokens) and tokens[pos] == "&":
            right, pos = parse_primary(pos + 1)
            left = ("and", left, right)
        return left, pos

    def parse_xor(pos):
        left, pos = parse_and(pos)
        while pos < len(tokens) and tokens[pos] == "^":
            right, pos = parse_and(pos + 1)
            left = ("xor", left, right)
        return left, pos

    def parse_or(pos):
        left, pos = parse_xor(pos)
        while pos < len(tokens) and tokens[pos] == "|":
            right, pos = parse_xor(pos + 1)
            left = ("or", left, right)
        return left, pos

    def parse_eq(pos):
        left, pos = parse_or(pos)
        while pos < len(tokens) and tokens[pos] in ("==", "!="):
            op = tokens[pos]
            right, pos = parse_or(pos + 1)
            left = (op, left, right)
        return left, pos

    def parse_expr(pos):
        return parse_eq(pos)

    node, pos = parse_expr(0)
    if pos != len(tokens):
        raise ValueError("Unexpected tokens at end of expression: %s" % tokens[pos:])
    return node


def _const_to_bool(token):
    if token in ("1", "1'b1", "1'B1"):
        return "true"
    if token in ("0", "1'b0", "1'B0"):
        return "false"
    return None


def _smt2_const(value, width, type_hint):
    if type_hint and type_hint[0] == "Bool":
        return "true" if value else "false"
    if width is None and type_hint and type_hint[0] == "BitVec":
        width = type_hint[1]
    if width is None:
        if value in (0, 1):
            return "true" if value else "false"
        raise ValueError("Cannot determine width for constant: %s" % value)
    mask = (1 << width) - 1
    return "(_ bv%d %d)" % (value & mask, width)


def _ast_to_smt2(
    ast, signal_map, state_name, alias_cache=None, const_map=None, type_map=None, type_hint=None
):
    if isinstance(ast, tuple):
        op = ast[0]
        if op == "not":
            return "(not %s)" % _ast_to_smt2(
                ast[1],
                signal_map,
                state_name,
                alias_cache,
                const_map,
                type_map,
                ("Bool", 1),
            )
        if op in ("and", "or", "xor"):
            return "(%s %s %s)" % (
                op,
                _ast_to_smt2(
                    ast[1],
                    signal_map,
                    state_name,
                    alias_cache,
                    const_map,
                    type_map,
                    ("Bool", 1),
                ),
                _ast_to_smt2(
                    ast[2],
                    signal_map,
                    state_name,
                    alias_cache,
                    const_map,
                    type_map,
                    ("Bool", 1),
                ),
            )
        if op == "==":
            left_hint = None
            right_hint = None
            if not isinstance(ast[1], tuple) and type_map:
                left_hint = type_map.get(ast[1])
            if not isinstance(ast[2], tuple) and type_map:
                right_hint = type_map.get(ast[2])
            if left_hint is None:
                left_hint = right_hint
            if right_hint is None:
                right_hint = left_hint
            return "(= %s %s)" % (
                _ast_to_smt2(
                    ast[1],
                    signal_map,
                    state_name,
                    alias_cache,
                    const_map,
                    type_map,
                    left_hint,
                ),
                _ast_to_smt2(
                    ast[2],
                    signal_map,
                    state_name,
                    alias_cache,
                    const_map,
                    type_map,
                    right_hint,
                ),
            )
        if op == "!=":
            left_hint = None
            right_hint = None
            if not isinstance(ast[1], tuple) and type_map:
                left_hint = type_map.get(ast[1])
            if not isinstance(ast[2], tuple) and type_map:
                right_hint = type_map.get(ast[2])
            if left_hint is None:
                left_hint = right_hint
            if right_hint is None:
                right_hint = left_hint
            return "(not (= %s %s))" % (
                _ast_to_smt2(
                    ast[1],
                    signal_map,
                    state_name,
                    alias_cache,
                    const_map,
                    type_map,
                    left_hint,
                ),
                _ast_to_smt2(
                    ast[2],
                    signal_map,
                    state_name,
                    alias_cache,
                    const_map,
                    type_map,
                    right_hint,
                ),
            )
        raise ValueError("Unsupported AST op: %s" % op)
    const = _const_to_bool(ast)
    if const is not None:
        return const
    parsed = _parse_sv_int_literal(ast)
    if parsed is None and re.fullmatch(r"\\d+", ast):
        parsed = (int(ast), None)
    if parsed is None and const_map:
        parsed = const_map.get(ast)
    if parsed is not None:
        value, width = parsed
        return _smt2_const(value, width, type_hint)
    if ast not in signal_map:
        if alias_cache is None:
            alias_cache = {}
        resolved = _resolve_signal_alias(ast, signal_map, alias_cache)
        if resolved:
            return "(%s %s)" % (signal_map[resolved], state_name)
        raise ValueError("Signal not found in SMT2 model: %s" % ast)
    return "(%s %s)" % (signal_map[ast], state_name)


def _build_bmc_smt2(
    smt2_text,
    top_module,
    signal_map,
    antecedent,
    consequent,
    delay,
    signal_types=None,
    const_map=None,
    start_state=0,
    assumptions=None,
    signal_widths=None,
):
    state_sort = "%s_s" % top_module
    if start_state < 0:
        start_state = 0
    total_states = start_state + delay + 1
    states = ["s%d" % i for i in range(total_states)]
    lines = [smt2_text]
    for state in states:
        lines.append("(declare-const %s |%s|)" % (state, state_sort))
        lines.append("(assert (|%s_h| %s))" % (top_module, state))
        lines.append("(assert (|%s_a| %s))" % (top_module, state))
        lines.append("(assert (|%s_u| %s))" % (top_module, state))
    lines.append("(assert (|%s_i| %s))" % (top_module, states[0]))
    for idx in range(len(states) - 1):
        lines.append(
            "(assert (|%s_t| %s %s))" % (top_module, states[idx], states[idx + 1])
        )
    _emit_assumptions(
        lines,
        assumptions,
        signal_map,
        signal_types,
        const_map,
        signal_widths,
        states,
    )
    ant_ast = _parse_expr(_tokenize_expr(antecedent))
    cons_ast = _parse_expr(_tokenize_expr(consequent))
    alias_cache = {}
    ant_state = states[start_state]
    cons_state = states[start_state + delay]
    ant_expr = _ast_to_smt2(
        ant_ast,
        signal_map,
        ant_state,
        alias_cache,
        const_map,
        signal_types,
        ("Bool", 1),
    )
    cons_expr = _ast_to_smt2(
        cons_ast,
        signal_map,
        cons_state,
        alias_cache,
        const_map,
        signal_types,
        ("Bool", 1),
    )
    lines.append("(assert (and %s (not %s)))" % (ant_expr, cons_expr))
    return "\n".join(lines)


def _check_smt2_sat(smt2_text):
    solver = z3.Solver()
    solver.from_string(smt2_text)
    return solver.check() == z3.sat


def _check_full_model_with_yosys(
    verilog_files,
    top_module,
    depth,
    include_dirs=None,
    script_path=None,
):
    if script_path is None:
        script_path = os.path.join(os.path.dirname(__file__), "yosys_assert_bmc.py")
    if not os.path.isfile(script_path):
        raise FileNotFoundError("yosys_assert_bmc.py not found: %s" % script_path)
    cmd = [sys.executable, script_path, "-m", top_module, "--depth", str(depth)]
    if include_dirs:
        for inc in include_dirs:
            cmd.extend(["-I", inc])
    cmd.extend(verilog_files)
    result = subprocess.run(cmd, capture_output=True, text=True, check=False)
    output = (result.stdout + "\n" + result.stderr).strip()
    if result.returncode != 0:
        raise RuntimeError("yosys_assert_bmc.py failed:\n%s" % output)
    for line in output.splitlines():
        line = line.strip()
        if line.startswith("Assertions violated within depth"):
            return True
        if line.startswith("No assertion violation up to depth"):
            return False
        if line.startswith("Solver returned unknown"):
            return None
    return None


def _build_bmc_smt2_from_property(
    smt2_text,
    top_module,
    property_expr,
    max_state_idx,
    signal_map=None,
    signal_types=None,
    const_map=None,
    assumptions=None,
    signal_widths=None,
):
    state_sort = "%s_s" % top_module
    states = ["s%d" % i for i in range(max_state_idx + 1)]
    lines = [smt2_text]
    for state in states:
        lines.append("(declare-const %s |%s|)" % (state, state_sort))
        lines.append("(assert (|%s_h| %s))" % (top_module, state))
        lines.append("(assert (|%s_a| %s))" % (top_module, state))
        lines.append("(assert (|%s_u| %s))" % (top_module, state))
    lines.append("(assert (|%s_i| %s))" % (top_module, states[0]))
    for idx in range(len(states) - 1):
        lines.append(
            "(assert (|%s_t| %s %s))" % (top_module, states[idx], states[idx + 1])
        )
    _emit_assumptions(
        lines,
        assumptions,
        signal_map,
        signal_types,
        const_map,
        signal_widths,
        states,
    )
    lines.append("(assert %s)" % property_expr)
    return "\n".join(lines)


def _sva2smt_property_expr(
    assertion_expr,
    top_module,
    signal_map,
    delay,
    sva2smt_bin,
):
    if not sva2smt_bin or not os.path.isfile(sva2smt_bin):
        raise FileNotFoundError("sva2smt binary not found: %s" % sva2smt_bin)
    stripped = _strip_sv_comments(assertion_expr)
    stripped = re.sub(r"@\s*\([^)]*\)", "", stripped).strip()
    temp_dir = tempfile.mkdtemp(prefix="sva2smt_")
    sva_path = os.path.join(temp_dir, "assertion.sv")
    out_path = os.path.join(temp_dir, "property.smt2")
    with open(sva_path, "w", encoding="utf-8") as handle:
        handle.write("module %s();\n" % top_module)
        handle.write("  assert property (%s);\n" % stripped)
        handle.write("endmodule\n")
    time_bound = 2 * (delay + 1) + 1
    cmd = [sva2smt_bin, sva_path, top_module, out_path, str(time_bound), "0"]
    result = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if result.returncode != 0:
        raise RuntimeError(
            "sva2smt failed:\n%s" % ((result.stdout + "\n" + result.stderr).strip())
        )
    with open(out_path, "r", encoding="utf-8") as handle:
        output = handle.read()
    expr = None
    for line in output.splitlines():
        line = line.strip()
        match = re.match(r"^\(assert\s+\(=\s+Assert_1\s+(.*)\)\)$", line)
        if match:
            expr = match.group(1)
            break
    if expr is None:
        raise ValueError("sva2smt output missing Assert_1 expression")
    max_state_idx = 0

    def repl(match):
        nonlocal max_state_idx
        sig = match.group(1)
        time = int(match.group(2))
        idx = time // 2
        if idx > max_state_idx:
            max_state_idx = idx
        if sig not in signal_map:
            raise ValueError("Signal not found in SMT2 model: %s" % sig)
        return "(%s s%d)" % (signal_map[sig], idx)

    expr = re.sub(
        r"testbench\.[A-Za-z0-9_]+_instance\.([A-Za-z_][A-Za-z0-9_$]*)_(\d+)_1",
        repl,
        expr,
    )
    expr = expr.replace("#b1", "true").replace("#b0", "false")
    max_state_idx = max(max_state_idx, delay)
    return expr, max_state_idx


def _reverse_distances(dep_g, targets):
    dist = {}
    queue = []
    for target in targets:
        if target in dep_g:
            dist[target] = 0
            queue.append(target)
    while queue:
        node = queue.pop(0)
        for pred in dep_g.predecessors(node):
            if pred not in dist:
                dist[pred] = dist[node] + 1
                queue.append(pred)
    return dist


def _depth_sequence(state_vars, dist, start_depth=None, max_iter=None):
    depths = sorted({dist[v] for v in state_vars if v in dist})
    if not depths:
        return []
    if start_depth is None:
        start_depth = depths[0]
    if start_depth not in depths:
        higher = [d for d in depths if d > start_depth]
        start_depth = higher[0] if higher else depths[-1]
    start_idx = depths.index(start_depth)
    seq = depths[start_idx:]
    if max_iter is not None:
        seq = seq[:max_iter]
    return seq


def run_cegar(
    verilog_files,
    top_module,
    assertion_expr,
    targets,
    include_dirs=None,
    clocks=None,
    a1_depth=None,
    a1_max_state=None,
    max_iter=None,
    use_sva2smt=False,
    sva2smt_bin=None,
    sva_max_time=None,
    assumption_exprs=None,
):
    LOG.info("CEGAR start: targets=%s", ",".join(targets))
    result = extract_coi(
        verilog_files,
        top_module=top_module,
        targets=targets,
        include_dirs=include_dirs,
        clocks=clocks,
        temporal_depth=1,
        strip_assertions=True,
    )
    module_files = _map_module_files(verilog_files)
    module_line_offsets = _compute_module_line_offsets(
        result["elaborate_info"], module_files
    )
    dep_g = result["dep_g"]
    state_vars = collect_state_vars(
        result["elaborate_info"], result["top_module"], result["scope_module_map"]
    )
    LOG.info("State vars in COI: %d", len(state_vars))
    dist = _reverse_distances(dep_g, targets)
    if a1_max_state is not None and a1_depth is None:
        _, _, a1_depth = compute_a1_for_targets(
            dep_g, targets, state_vars, max_state=a1_max_state
        )
    depths = _depth_sequence(state_vars, dist, a1_depth, max_iter)
    no_state = False
    if not depths:
        no_state = True
        LOG.info("No state vars in COI; falling back to full check")
    else:
        LOG.info("CEGAR depths: %s", depths)

    keep_signals = _derive_keep_signals(assertion_expr, targets)
    if keep_signals:
        LOG.info("Inject keep for signals: %s", ",".join(keep_signals))
    stripped_files = _prepare_verilog_files(verilog_files, keep_signals=keep_signals)
    work_dir = tempfile.mkdtemp(prefix="proof_core_cegar_")
    smt2_path = os.path.join(work_dir, "design.smt2")
    _run_yosys_smt2(
        stripped_files,
        top_module,
        smt2_path,
        include_dirs=include_dirs,
        flatten=_needs_flatten(assertion_expr) or no_state,
    )
    smt2_text = open(smt2_path, "r").read()
    topmod = _find_topmod(smt2_text) or top_module
    signal_map = _extract_signal_map(smt2_text, topmod)
    signal_types = _extract_signal_types(smt2_text, topmod)
    const_map = _extract_param_constants(verilog_files)
    signal_widths = _signal_widths_from_types(signal_types)
    stripped_expr = _strip_sv_comments(assertion_expr)
    has_clock_event = re.search(r"@\s*\(", stripped_expr) is not None
    start_state = 1 if (has_clock_event or (clocks and not has_clock_event)) else 0
    assumptions = []
    if assumption_exprs:
        ctx = Context(signal_map, signal_widths, 1)
        for raw_expr in assumption_exprs:
            norm = _normalize_assumption_expr(raw_expr)
            if not norm:
                LOG.warning("Assumption skipped (unsupported/empty): %s", raw_expr)
                continue
            parsed = False
            try:
                tokens = tokenize(norm)
                _rewrite_tokens_with_aliases(tokens, signal_map)
                parser = Parser(tokens)
                expr = parser.parse_expr()
                if parser.peek() is not None:
                    raise ParseError("Unexpected tokens in assumption")
                smt_expr, typ = expr.to_smt(0, ctx)
                if smt_expr is None:
                    raise ParseError("Assumption could not be translated")
                _cast_to_bool(smt_expr, typ)
                assumptions.append(("sva", expr))
                parsed = True
            except Exception:
                parsed = False
            if parsed:
                continue
            try:
                ast = _parse_expr(_tokenize_expr(norm))
            except Exception as err:
                LOG.warning("Assumption parse failed (%s): %s", err, raw_expr)
                continue
            try:
                _ast_to_smt2(
                    ast,
                    signal_map,
                    "s0",
                    {},
                    const_map,
                    signal_types,
                    ("Bool", 1),
                )
            except Exception as err:
                LOG.warning("Assumption unresolved (%s): %s", err, raw_expr)
                continue
            assumptions.append(("simple", ast))
    antecedent = None
    consequent = None
    delay = None
    property_expr = None
    property_state_max = None
    use_python_sva = _should_use_sva_parser(assertion_expr)
    if not use_python_sva:
        try:
            antecedent, consequent, delay = _parse_property(assertion_expr)
            property_state_max = delay
            LOG.info(
                "Property parsed: antecedent='%s' consequent='%s' delay=%d",
                antecedent,
                consequent,
                delay,
            )
        except Exception as err:
            LOG.warning("Property parse failed (%s), using python translator", err)
            use_python_sva = True
    if use_python_sva:
        try:
            property_expr, property_state_max = translate_sva_property(
                assertion_expr,
                smt2_text,
                topmod,
                signal_map,
                max_time=sva_max_time,
            )
            LOG.info("Property SMT2 generated by python translator")
        except Exception as py_err:
            LOG.warning("python translator failed (%s), falling back to simple parser", py_err)
            if antecedent is None:
                antecedent, consequent, delay = _parse_property(assertion_expr)
                property_state_max = delay
    if use_sva2smt and property_expr is None and delay is not None:
        try:
            property_expr, property_state_max = _sva2smt_property_expr(
                assertion_expr,
                topmod,
                signal_map,
                delay,
                sva2smt_bin,
            )
            LOG.info("Property SMT2 generated by sva2smt")
        except Exception as err:
            LOG.warning("sva2smt failed (%s)", err)
    LOG.info("SMT2 base path: %s", smt2_path)

    full_text = smt2_text
    if property_expr:
        full_bmc = _build_bmc_smt2_from_property(
            full_text,
            topmod,
            property_expr,
            property_state_max,
            signal_map=signal_map,
            signal_types=signal_types,
            const_map=const_map,
            assumptions=assumptions,
            signal_widths=signal_widths,
        )
    else:
        full_bmc = _build_bmc_smt2(
            full_text,
            topmod,
            signal_map,
            antecedent,
            consequent,
            delay,
            signal_types=signal_types,
            const_map=const_map,
            start_state=start_state,
            assumptions=assumptions,
            signal_widths=signal_widths,
        )
    full_bmc_path = os.path.join(work_dir, "full_bmc.smt2")
    _write_text(full_bmc_path, full_bmc)
    LOG.info("Full BMC SMT2: %s", full_bmc_path)

    if no_state:
        full_sat = _check_smt2_sat(full_bmc)
        LOG.info("No-state full SAT=%s", full_sat)
        if full_sat:
            return "fail", None, 0, None
        kept_nodes = set(dist.keys()) if dist else set(targets)
        resolved_kept = set()
        alias_cache = {}
        for node in kept_nodes:
            if not node:
                continue
            resolved = _resolve_signal_alias(node, signal_map, alias_cache)
            resolved_kept.add(resolved or node)
        coverage = _collect_proof_core_coverage(
            resolved_kept,
            result["elaborate_info"],
            result["top_module"],
            result["scope_module_map"],
            module_files,
            module_line_offsets=module_line_offsets,
            include_dirs=include_dirs,
        )
        return "proved", resolved_kept, 0, coverage

    pure_comb = (
        property_expr is None
        and delay == 0
        and antecedent is not None
        and consequent is not None
        and not re.search(r"\|->|\|=>|##|\bthroughout\b|\$", stripped_expr)
    )
    if pure_comb and not assumptions:
        full_sat = _check_smt2_sat(full_bmc)
        LOG.info("Pure combinational invariant; full SAT=%s", full_sat)
        if full_sat:
            return "fail", None, 0, None
        return "proved", [], 0, None

    for depth in depths:
        a1, kept, _ = compute_a1_for_targets(dep_g, targets, state_vars, depth=depth)
        kept_regs = {reg for reg in state_vars if reg in kept}
        LOG.info("Depth %d: A-nodes=%d kept regs=%d kept nodes=%d", depth, len(a1), len(kept_regs), len(kept))
        LOG.info("Depth %d: A-nodes list: %s", depth, ",".join(sorted(a1)))
        LOG.info("Depth %d: kept nodes list: %s", depth, ",".join(sorted(kept)))
        abstract_text = _rewrite_transition(smt2_text, topmod, kept_regs)
        abstract_path = os.path.join(work_dir, "abstract_depth_%d.smt2" % depth)
        _write_text(abstract_path, abstract_text)
        LOG.info("Depth %d: abstract SMT2 path: %s", depth, abstract_path)
        if property_expr:
            abstract_bmc = _build_bmc_smt2_from_property(
                abstract_text,
                topmod,
                property_expr,
                property_state_max,
                signal_map=signal_map,
                signal_types=signal_types,
                const_map=const_map,
                assumptions=assumptions,
                signal_widths=signal_widths,
            )
        else:
            abstract_bmc = _build_bmc_smt2(
                abstract_text,
                topmod,
                signal_map,
                antecedent,
                consequent,
                delay,
                signal_types=signal_types,
                const_map=const_map,
                assumptions=assumptions,
                signal_widths=signal_widths,
            )
        abstract_bmc_path = os.path.join(work_dir, "abstract_depth_%d_bmc.smt2" % depth)
        _write_text(abstract_bmc_path, abstract_bmc)
        LOG.info("Depth %d: abstract BMC SMT2: %s", depth, abstract_bmc_path)
        abstract_sat = _check_smt2_sat(abstract_bmc)
        LOG.info("Depth %d: abstract SAT=%s", depth, abstract_sat)
        if not abstract_sat:
            coverage = _collect_proof_core_coverage(
                kept,
                result["elaborate_info"],
                result["top_module"],
                result["scope_module_map"],
                module_files,
                module_line_offsets=module_line_offsets,
                include_dirs=include_dirs,
            )
            return "proved", kept, depth, coverage
        full_sat = None
        delay_for_full = delay if delay is not None else property_state_max
        if delay_for_full is None:
            delay_for_full = 1
        full_depth = max(delay_for_full, 1)
        try:
            full_sat = _check_full_model_with_yosys(
                verilog_files,
                top_module=top_module,
                depth=full_depth,
                include_dirs=include_dirs,
            )
            LOG.info("Depth %d: full SAT (yosys_assert_bmc)=%s", depth, full_sat)
        except Exception as err:
            LOG.warning("Depth %d: yosys_assert_bmc failed (%s), falling back to SMT2+Z3", depth, err)
            full_sat = _check_smt2_sat(full_bmc)
            LOG.info("Depth %d: full SAT (fallback)=%s", depth, full_sat)
        if full_sat:
            return "fail", None, depth, None
        LOG.info(
            "Depth %d: spurious CEX (abstract SAT, full UNSAT), refining",
            depth,
        )
    return "unknown", None, depths[-1], None


def _build_arg_parser():
    parser = argparse.ArgumentParser(description="CEGAR proof core generator (SMT2+Z3).")
    parser.add_argument("-m", "--module", dest="top", required=True)
    parser.add_argument("-I", "--include", dest="include", action="append", default=[])
    parser.add_argument("-c", "--clock", dest="clock", default="DEFAULT_CLOCK:1")
    parser.add_argument("-f", "--files", dest="file_loc", help="Directory with .v files")
    parser.add_argument("-F", "--file-list", dest="lfile", help="File containing .v file paths")
    parser.add_argument("--ext", dest="extension", default="*.v")
    parser.add_argument("--assertion-file", help="Assertion file to parse instead of design")
    parser.add_argument("--a1-depth", type=int, help="Initial abstraction depth")
    parser.add_argument("--a1-max-state", type=int, help="Max kept state vars in A1")
    parser.add_argument("--max-iter", type=int, help="Max CEGAR iterations")
    parser.add_argument(
        "--assume-file",
        action="append",
        default=[],
        help=(
            "Assumption file(s) with one expression per line (no temporal operators). "
            "Optional prefix: 'assertion_N:' or '*:' to scope assumptions."
        ),
    )
    parser.add_argument("--use-sva2smt", action="store_true", help="Use sva2smt for SVA translation")
    parser.add_argument("--sva2smt-bin", help="Path to sva2smt binary")
    parser.add_argument("--sva-max-time", type=int, help="Max time bound for python SVA translation")
    parser.add_argument("--log-file", default="proof_core_cegar.log", help="Write log file path")
    parser.add_argument(
        "--rewrite-module-prefixes",
        action="store_true",
        help=(
            "Rewrite module-name prefixes in assertion expressions to instance paths "
            "(top module prefix stripped). Expands assertions for multiple instances."
        ),
    )
    parser.add_argument(
        "--max-expansions",
        type=int,
        default=256,
        help="Max expanded assertion variants when rewriting module prefixes",
    )
    parser.add_argument(
        "--coverage-only",
        action="store_true",
        help="Only print coverage lines (format: S|B <assertion> <file:line>)",
    )
    parser.add_argument("verilog_files", nargs="*", help="Explicit Verilog file paths")
    return parser


def _collect_verilog_files(file_loc=None, file_list=None, verilog_files=None, extension="*.v"):
    vfiles = []
    if verilog_files:
        vfiles.extend(verilog_files)
    if file_loc:
        for root, _, file_names in os.walk(file_loc):
            for file_name in file_names:
                if re.fullmatch(extension.replace(".", r"\.").replace("*", ".*"), file_name):
                    vfiles.append(os.path.join(root, file_name))
    if file_list and os.path.isfile(file_list):
        with open(file_list, "r") as handle:
            for line in handle.readlines():
                line = line.strip()
                if not line or line.startswith("#") or line.startswith("//"):
                    continue
                vfiles.append(line)
    return list(dict.fromkeys(vfiles))


def main():
    parser = _build_arg_parser()
    args = parser.parse_args()
    _setup_logger(args.log_file)
    global QUIET_OUTPUT
    QUIET_OUTPUT = bool(args.coverage_only)
    LOG.info("Starting proof_core_cegar")
    LOG.info("Top module: %s", args.top)

    vfiles = _collect_verilog_files(
        file_loc=args.file_loc,
        file_list=args.lfile,
        verilog_files=args.verilog_files,
        extension=args.extension,
    )
    if not vfiles:
        parser.error("No Verilog files found.")
    LOG.info("Verilog files: %s", ", ".join(vfiles))

    module_to_scopes = None
    if args.rewrite_module_prefixes:
        module_to_scopes = _build_module_instance_map(
            vfiles, args.top, args.include, args.clock
        )

    if args.assertion_file:
        expressions = _extract_assertion_expressions_from_file(args.assertion_file)
        if args.rewrite_module_prefixes:
            expressions, labels = _rewrite_expressions_with_instance_scopes(
                expressions,
                module_to_scopes,
                max_expansions=args.max_expansions,
            )
            assertion_groups = _build_assertion_groups_from_expressions(
                expressions, labels=labels
            )
        else:
            assertion_groups, _ = extract_assertion_targets(
                vfiles, assertion_file=args.assertion_file
            )
    else:
        assertion_groups, _ = extract_assertion_targets(vfiles)
        expressions = []
        for vfile in vfiles:
            expressions.extend(
                _extract_assertion_expressions_from_text(open(vfile, "r").read())
            )
    if not assertion_groups:
        parser.error("No assertions found.")
    if len(expressions) < len(assertion_groups):
        parser.error("Assertion expressions could not be fully parsed.")
    LOG.info("Found %d assertions", len(assertion_groups))

    assumption_entries = []
    for path in args.assume_file:
        assumption_entries.extend(_extract_assumption_expressions_from_file(path))
    has_assumption_labels = any(label is not None for label, _ in assumption_entries)
    if args.rewrite_module_prefixes and assumption_entries:
        expanded = []
        for label, expr in assumption_entries:
            exprs, _ = _rewrite_expressions_with_instance_scopes(
                [expr],
                module_to_scopes,
                max_expansions=args.max_expansions,
            )
            for e in exprs:
                expanded.append((label, e))
        assumption_entries = expanded

    coverage_intersection = None
    coverage_assertions = 0
    for idx, (label, targets) in enumerate(assertion_groups):
        assertion_label = label
        expr = expressions[idx]
        LOG.info("Assertion %s targets: %s", assertion_label, ",".join(targets))
        LOG.info("Assertion %s expr: %s", assertion_label, expr)
        sva2smt_bin = args.sva2smt_bin
        if args.use_sva2smt and sva2smt_bin is None:
            sva2smt_bin = os.path.join(os.path.dirname(__file__), "sva2smt", "sva2smt")
        if args.coverage_only:
            if assumption_entries:
                if has_assumption_labels:
                    assumption_exprs = [
                        expr
                        for assume_label, expr in assumption_entries
                        if (
                            assume_label == "*"
                            or assume_label == assertion_label
                            or (
                                assume_label
                                and assertion_label.startswith(assume_label + "__")
                            )
                        )
                    ]
                else:
                    if idx == 0 and len(assertion_groups) > 1:
                        LOG.warning(
                            "Assumptions have no labels; applying globally to all assertions. "
                            "Use 'assertion_N:' or '*:' to scope."
                        )
                    assumption_exprs = [expr for _, expr in assumption_entries]
            else:
                assumption_exprs = []
            with redirect_stdout(io.StringIO()):
                status, kept, depth, coverage = run_cegar(
                    vfiles,
                    top_module=args.top,
                    assertion_expr=expr,
                    targets=targets,
                    include_dirs=args.include,
                    clocks=args.clock,
                    a1_depth=args.a1_depth,
                    a1_max_state=args.a1_max_state,
                    max_iter=args.max_iter,
                    use_sva2smt=args.use_sva2smt,
                    sva2smt_bin=sva2smt_bin,
                    sva_max_time=args.sva_max_time,
                    assumption_exprs=assumption_exprs,
                )
        else:
            if assumption_entries:
                if has_assumption_labels:
                    assumption_exprs = [
                        expr
                        for assume_label, expr in assumption_entries
                        if (
                            assume_label == "*"
                            or assume_label == assertion_label
                            or (
                                assume_label
                                and assertion_label.startswith(assume_label + "__")
                            )
                        )
                    ]
                else:
                    if idx == 0 and len(assertion_groups) > 1:
                        LOG.warning(
                            "Assumptions have no labels; applying globally to all assertions. "
                            "Use 'assertion_N:' or '*:' to scope."
                        )
                    assumption_exprs = [expr for _, expr in assumption_entries]
            else:
                assumption_exprs = []
            status, kept, depth, coverage = run_cegar(
                vfiles,
                top_module=args.top,
                assertion_expr=expr,
                targets=targets,
                include_dirs=args.include,
                clocks=args.clock,
                a1_depth=args.a1_depth,
                a1_max_state=args.a1_max_state,
                max_iter=args.max_iter,
                use_sva2smt=args.use_sva2smt,
                sva2smt_bin=sva2smt_bin,
                sva_max_time=args.sva_max_time,
                assumption_exprs=assumption_exprs,
            )
        if status == "proved":
            LOG.info("Assertion %s proved at depth %d (kept %d nodes)", label, depth, len(kept))
            if args.coverage_only:
                if coverage:
                    _emit_coverage_only(label, coverage)
                else:
                    print(
                        "Assertion %s: no proof core coverage available" % label,
                        file=sys.stderr,
                    )
            else:
                print(
                    "Assertion %s: ProofCore depth %d, kept nodes %d"
                    % (label, depth, len(kept))
                )
                for node in sorted(kept):
                    print(node)
                if coverage:
                    stmt_cov, branch_cov = coverage
                    print(
                        "Assertion %s: Statement coverage %d" % (label, len(stmt_cov))
                    )
                    for loc in sorted(stmt_cov):
                        print(loc)
                    print(
                        "Assertion %s: Branch coverage %d" % (label, len(branch_cov))
                    )
                    for loc in sorted(branch_cov):
                        print(loc)
                    combined_cov = stmt_cov | branch_cov
                    if coverage_intersection is None:
                        coverage_intersection = set(combined_cov)
                    else:
                        coverage_intersection &= combined_cov
                    coverage_assertions += 1
        elif status == "fail":
            LOG.info("Assertion %s has real counterexample at depth %d", label, depth)
            if args.coverage_only:
                print(
                    "Assertion %s: real counterexample found at depth %d" % (label, depth),
                    file=sys.stderr,
                )
            else:
                print(
                    "Assertion %s: real counterexample found at depth %d" % (label, depth)
                )
        else:
            LOG.info("Assertion %s did not converge (status=%s)", label, status)
            if args.coverage_only:
                print(
                    "Assertion %s: unable to converge (status=%s)" % (label, status),
                    file=sys.stderr,
                )
            else:
                print("Assertion %s: unable to converge (status=%s)" % (label, status))
    if not args.coverage_only:
        if coverage_intersection is not None:
            print(
                "Assertions combined coverage intersection %d (from %d assertions)"
                % (len(coverage_intersection), coverage_assertions)
            )
            for loc in sorted(coverage_intersection):
                print(loc)
        else:
            print("Assertions combined coverage intersection 0 (no proof core coverage)")
    LOG.info("Log written to %s", args.log_file)


if __name__ == "__main__":
    main()
