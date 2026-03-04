#!/usr/bin/env python3
import argparse
import fnmatch
import os
import re
import tempfile
from collections import deque
import networkx as nx
from verilog import parse_verilog, get_modules, get_ports, getDefUseTarget, get_params, analyze_pagerank
from static_analysis import CDFG, Linking, cone_of_influence
try:
    from slang_static_analysis import build_elaborate_info as build_elaborate_info_slang
except Exception:  # pragma: no cover - optional dependency
    build_elaborate_info_slang = None


def _normalize_clocks(clock_spec):
    if not clock_spec:
        return {"DEFAULT_CLOCK": "1"}
    if isinstance(clock_spec, dict):
        return clock_spec if clock_spec else {"DEFAULT_CLOCK": "1"}
    if isinstance(clock_spec, (list, tuple, set)):
        return {str(clk): "1" for clk in clock_spec}
    if isinstance(clock_spec, str):
        if ":" in clock_spec:
            name, edge = clock_spec.split(":", 1)
            return {name: edge or "1"}
        return {clock_spec: "1"}
    raise TypeError("Unsupported clock spec: %r" % (clock_spec,))


def _normalize_includes(include_dirs):
    if not include_dirs:
        return []
    include_dirs_ = []
    for inc in include_dirs:
        if os.path.isdir(inc):
            include_dirs_.append(os.path.abspath(inc))
    return include_dirs_

def _unique(items):
    seen = set()
    uniq = []
    for item in items:
        if item not in seen:
            seen.add(item)
            uniq.append(item)
    return uniq

def _get_file_names_from_loc(root_dir, extension):
    name_of_files = []
    for root, _, file_names in os.walk(root_dir):
        for file_name in fnmatch.filter(file_names, extension):
            name_of_files.append(os.path.abspath(os.path.join(root, file_name)))
    return name_of_files


def _get_file_names_from_file(lfile):
    vfiles = []
    with open(lfile, "r") as handle:
        for line_ in handle.readlines():
            line = line_.strip()
            if not line:
                continue
            if line.startswith("#") or line.startswith("//"):
                continue
            if os.path.isfile(line):
                vfiles.append(os.path.abspath(line))
    return vfiles


def _get_targets(targets):
    targets_ = []
    for target in targets.split(","):
        targets_.append(target)
    return targets_


def _collect_verilog_files(file_loc=None, file_list=None, verilog_files=None, extension="*.v"):
    vfiles = []
    if verilog_files:
        for vfile in verilog_files:
            if os.path.isfile(vfile):
                vfiles.append(os.path.abspath(vfile))
            else:
                raise FileNotFoundError("Verilog file not found: %s" % vfile)
    if file_loc:
        vfiles.extend(_get_file_names_from_loc(file_loc, extension))
    if file_list:
        vfiles.extend(_get_file_names_from_file(file_list))

    return _unique(vfiles)


def _infer_top_module(module_defs, module_instances):
    top_candidates = sorted(set(module_defs) - set(module_instances))
    return top_candidates


def _resolve_target_name(target, dep_g):
    if target in dep_g:
        return [target], False
    candidates = [n for n in dep_g.nodes() if n.endswith("." + target)]
    if len(candidates) == 1:
        return candidates, True
    if not candidates:
        return [], True
    return sorted(candidates), True

SV_KEYWORDS = {
    "always", "and", "assert", "assign", "assume", "automatic", "begin", "case",
    "casex", "casez", "clocking", "cover", "default", "disable", "else", "end",
    "endcase", "endclocking", "endproperty", "endsequence", "eventually",
    "for", "forever", "iff", "if", "implies", "inside", "join", "local", "logic",
    "module", "negedge", "not", "or", "posedge", "property", "sequence", "strong",
    "then", "throughout", "until", "unique", "weak", "within", "xor",
}


def _strip_sv_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.DOTALL)
    text = re.sub(r"//.*", " ", text)
    return text


def _extract_property_blocks(text):
    properties = {}
    prop_re = re.compile(r"\bproperty\s+([A-Za-z_][A-Za-z0-9_]*)\b")
    idx = 0
    while True:
        match = prop_re.search(text, idx)
        if not match:
            break
        name = match.group(1)
        body_start = match.end()
        body_end = text.find("endproperty", body_start)
        if body_end == -1:
            break
        body = text[body_start:body_end]
        properties[name] = body
        idx = body_end + len("endproperty")
    return properties


def _extract_balanced_parens(text, start_idx):
    depth = 0
    start = None
    for idx in range(start_idx, len(text)):
        char = text[idx]
        if char == "(":
            if depth == 0:
                start = idx + 1
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0 and start is not None:
                return text[start:idx], idx + 1
    return "", start_idx


def _extract_assertion_expressions_from_text(text):
    expressions = []
    stripped = _strip_sv_comments(text)
    properties = _extract_property_blocks(stripped)
    assert_re = re.compile(r"\bassert\b")
    idx = 0
    while True:
        match = assert_re.search(stripped, idx)
        if not match:
            break
        pos = match.start()
        tail = stripped[pos:]
        prop_match = re.match(r"\bassert\s+property\b", tail)
        if prop_match:
            paren_idx = tail.find("(", prop_match.end())
            if paren_idx != -1:
                expr, end_idx = _extract_balanced_parens(tail, paren_idx)
                expr = expr.strip()
                if expr in properties:
                    expr = properties[expr]
                expressions.append(expr)
                idx = pos + end_idx
                continue
        paren_idx = tail.find("(")
        if paren_idx != -1:
            expr, end_idx = _extract_balanced_parens(tail, paren_idx)
            expressions.append(expr)
            idx = pos + end_idx
        else:
            idx = pos + len("assert")
    return expressions


def _extract_assertion_expressions_from_file(path):
    expressions = []
    with open(path, "r") as handle:
        for line in handle.readlines():
            raw = line.strip()
            if not raw:
                continue
            if raw.startswith("#") or raw.startswith("//") or raw.startswith("-"):
                continue
            if ":" in raw:
                _, raw = raw.split(":", 1)
            raw = raw.strip().rstrip(";")
            if raw:
                expressions.append(raw)
    return expressions


def _extract_targets_from_expression(expr):
    expr = re.sub(r"@\s*\([^)]*\)", " ", expr)
    expr = re.sub(r"\d+'[bdh][0-9a-fA-F_xXzZ]+", " ", expr)
    expr = re.sub(r"\b\d+\b", " ", expr)
    expr = re.sub(r"\$[A-Za-z_][A-Za-z0-9_]*", " ", expr)
    tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_\\.]*", expr)
    targets = [tok for tok in tokens if tok not in SV_KEYWORDS]
    return _unique(targets)


def extract_assertion_targets(verilog_files, assertion_file=None):
    expressions = []
    if assertion_file:
        expressions = _extract_assertion_expressions_from_file(assertion_file)
    else:
        for vfile in verilog_files:
            with open(vfile, "r") as handle:
                expressions.extend(_extract_assertion_expressions_from_text(handle.read()))
    targets = []
    labeled = []
    for idx, expr in enumerate(expressions):
        expr_targets = _extract_targets_from_expression(expr)
        label = "assertion_%d" % (idx + 1)
        labeled.append((label, expr_targets))
        targets.extend(expr_targets)
    return labeled, _unique(targets)

def collect_state_vars(elaborate_info, top_module, scope_module_map):
    state_vars = set()

    def add_module_vars(module_name, scope_prefix):
        var_def_chain = elaborate_info[module_name]["var_def_chain"]
        for var, info in var_def_chain.items():
            if info.get("Clocked"):
                if scope_prefix:
                    state_vars.add(scope_prefix + "." + var)
                else:
                    state_vars.add(var)

    add_module_vars(top_module, "")
    for scope, module_name in scope_module_map.items():
        add_module_vars(module_name, scope)

    return state_vars


def reverse_distances(dep_g, targets):
    dist = {}
    queue = deque()
    for target in targets:
        if target in dep_g and target not in dist:
            dist[target] = 0
            queue.append(target)

    while queue:
        node = queue.popleft()
        for pred in dep_g.predecessors(node):
            if pred not in dist:
                dist[pred] = dist[node] + 1
                queue.append(pred)

    return dist


def choose_a1(state_vars, dist, depth=None, max_state=None):
    candidates = sorted((dist[v], v) for v in state_vars if v in dist)
    if not candidates:
        return set(), set(), None

    if depth is None:
        if max_state is None:
            depth = candidates[0][0]
        else:
            running = 0
            depth = candidates[0][0]
            for d, _ in candidates:
                if d > depth:
                    if running >= max_state:
                        break
                    depth = d
                running += 1
            if running < max_state:
                depth = candidates[-1][0]
    else:
        candidate_depths = sorted({d for d, _ in candidates})
        if depth not in candidate_depths:
            higher = [d for d in candidate_depths if d > depth]
            if higher:
                depth = higher[0]
            else:
                depth = candidate_depths[-1]

    a1 = {v for v in state_vars if dist.get(v) == depth}
    kept = {node for node, d in dist.items() if d <= depth}
    return a1, kept, depth


def compute_a1_for_targets(dep_g, targets, state_vars, depth=None, max_state=None):
    dist = reverse_distances(dep_g, targets)
    return choose_a1(state_vars, dist, depth=depth, max_state=max_state)

def _strip_assertions_from_verilog(text):
    text = _strip_sv_comments(text)
    text = re.sub(r"\bproperty\b.*?\bendproperty\b\s*;?", " ", text, flags=re.DOTALL)
    text = re.sub(r"(?m)^\s*assert\b.*?;", " ", text)
    return text


def _prepare_verilog_files(verilog_files, strip_assertions=False):
    if not strip_assertions:
        return verilog_files
    temp_dir = tempfile.mkdtemp(prefix="coi_strip_")
    stripped_files = []
    for vfile in verilog_files:
        with open(vfile, "r") as handle:
            stripped = _strip_assertions_from_verilog(handle.read())
        out_path = os.path.join(temp_dir, os.path.basename(vfile))
        with open(out_path, "w") as handle:
            handle.write(stripped)
        stripped_files.append(out_path)
    return stripped_files


def _build_elaborate_info_pyverilog(verilog_files, include_dirs=None, clocks=None):
    include_dirs = _normalize_includes(include_dirs)
    clocks = _normalize_clocks(clocks)

    ast, _, _ = parse_verilog(verilog_files, include_dirs, [])

    module_defs = {}
    module_instances = {}
    get_modules(ast, module_defs, module_instances)

    if not module_defs:
        raise ValueError("No module definition found in the source verilog files")

    undefined_modules = set(module_instances.keys()) - set(module_defs.keys())
    if undefined_modules:
        raise ValueError(
            "Missing module definitions: %s" % ", ".join(sorted(undefined_modules))
        )

    elaborate_info = {}
    for module_name, module_ast in module_defs.items():
        params = get_params(module_ast, module_name)
        ports = get_ports(module_ast, module_name, params)
        _, _, targets = getDefUseTarget(ports)
        var_def_chain, var_use_chain, path_sets, dep_g, cdfgs, fused_info, modinsts = CDFG(
            module_ast, clocks, params, ports
        )
        elaborate_info[module_name] = {
            "params": params,
            "ports": ports,
            "targets": targets,
            "var_def_chain": var_def_chain,
            "var_use_chain": var_use_chain,
            "PathSets": path_sets,
            "dep_g": dep_g,
            "CDFGS": cdfgs,
            "fused_INFO": fused_info,
            "MODINSTS": modinsts,
            "module_lineno": getattr(module_ast, "lineno", None),
        }

    return elaborate_info, module_defs, module_instances


def build_elaborate_info(verilog_files, include_dirs=None, clocks=None, prefer_slang=True):
    if prefer_slang and build_elaborate_info_slang is not None:
        try:
            return build_elaborate_info_slang(
                verilog_files, include_dirs=include_dirs, clocks=clocks
            )
        except Exception as err:
            print("slang elaborate failed (%s), falling back to pyverilog" % err)
    return _build_elaborate_info_pyverilog(
        verilog_files, include_dirs=include_dirs, clocks=clocks
    )


def extract_coi(
    verilog_files,
    top_module=None,
    targets=None,
    include_dirs=None,
    clocks=None,
    temporal_depth=1,
    strip_assertions=False,
    prefer_slang=True,
):
    parse_files = _prepare_verilog_files(verilog_files, strip_assertions=strip_assertions)
    elaborate_info, module_defs, module_instances = build_elaborate_info(
        parse_files, include_dirs=include_dirs, clocks=clocks, prefer_slang=prefer_slang
    )

    if top_module:
        if top_module not in module_defs:
            raise ValueError("Top module not found: %s" % top_module)
    else:
        candidates = _infer_top_module(module_defs, module_instances)
        if len(candidates) != 1:
            raise ValueError(
                "Top module not specified. Candidates: %s" % ", ".join(candidates)
            )
        top_module = candidates[0]

    complete_dep_g, complete_fused_cdfg, scope_module_map = Linking(
        elaborate_info, top_module
    )

    if not targets:
        targets = elaborate_info[top_module]["targets"]

    pagerank = analyze_pagerank(complete_dep_g)

    resolved_targets = []
    target_map = {}
    for target in targets:
        resolved, auto = _resolve_target_name(target, complete_dep_g)
        if not resolved:
            continue
        resolved_targets.extend(resolved)
        if auto or resolved != [target]:
            target_map[target] = resolved
    resolved_targets = _unique(resolved_targets)
    if not resolved_targets:
        raise ValueError("No assertion targets resolved in dependency graph.")

    cones = cone_of_influence(
        resolved_targets,
        elaborate_info,
        complete_dep_g,
        pagerank,
        temporal_depth,
        top_module,
        scope_module_map,
    )

    return {
        "cones": cones,
        "top_module": top_module,
        "resolved_targets": resolved_targets,
        "target_map": target_map,
        "dep_g": complete_dep_g,
        "fused_cdfg": complete_fused_cdfg,
        "scope_module_map": scope_module_map,
        "elaborate_info": elaborate_info,
    }

def merge_cones(cones, targets):
    merged = nx.DiGraph()
    for target in targets:
        cone = cones.get(target)
        if cone:
            merged = nx.compose(merged, cone)
    return merged


def extract_assertion_coi(
    verilog_files,
    top_module=None,
    targets=None,
    include_dirs=None,
    clocks=None,
    temporal_depth=1,
    prefer_slang=True,
):
    result = extract_coi(
        verilog_files,
        top_module=top_module,
        targets=targets,
        include_dirs=include_dirs,
        clocks=clocks,
        temporal_depth=temporal_depth,
        strip_assertions=True,
        prefer_slang=prefer_slang,
    )
    merged = merge_cones(result["cones"], result["resolved_targets"])
    return merged, result


def _build_arg_parser():
    parser = argparse.ArgumentParser(
        description="Extract COI (cone of influence) for target signals."
    )
    parser.add_argument("-m", "--module", dest="top", help="Top module name")
    parser.add_argument("-t", "--targets", dest="targets", help="Target signals, comma separated")
    parser.add_argument("-I", "--include", dest="include", action="append", default=[])
    parser.add_argument("-c", "--clock", dest="clock", default="DEFAULT_CLOCK:1")
    parser.add_argument(
        "-d",
        "--temporal-depth",
        dest="temporal_depth",
        type=int,
        default=1,
        help="Maximum temporal depth for COI expansion",
    )
    parser.add_argument("-f", "--files", dest="file_loc", help="Directory with .v files")
    parser.add_argument("-F", "--file-list", dest="lfile", help="File containing .v file paths")
    parser.add_argument(
        "--ext",
        dest="extension",
        default="*.v",
        help="Extension pattern for --files (default: *.v)",
    )
    parser.add_argument(
        "--list-targets",
        action="store_true",
        help="List default target signals for the top module",
    )
    parser.add_argument(
        "--print-nodes",
        action="store_true",
        help="Print COI nodes for each target",
    )
    parser.add_argument(
        "--print-edges",
        action="store_true",
        help="Print COI edges for each target",
    )
    parser.add_argument(
        "--merge-targets",
        action="store_true",
        help="Merge COIs of all targets (assertion-style COI)",
    )
    parser.add_argument(
        "--assertion-coi",
        action="store_true",
        help="Extract COI from assertions found in the design",
    )
    parser.add_argument(
        "--assertion-file",
        help="Assertion file to parse instead of scanning Verilog",
    )
    parser.add_argument(
        "--no-slang",
        action="store_true",
        help="Disable slang parser and use pyverilog",
    )
    parser.add_argument(
        "--a1-depth",
        type=int,
        help="Initial abstraction depth (A1) based on dependency distance",
    )
    parser.add_argument(
        "--a1-max-state",
        type=int,
        help="Grow A1 until this many state variables are kept",
    )
    parser.add_argument(
        "--print-a1",
        action="store_true",
        help="Print the A1 cutset and kept-node count",
    )
    parser.add_argument("verilog_files", nargs="*", help="Explicit Verilog file paths")
    return parser


def main():
    parser = _build_arg_parser()
    args = parser.parse_args()

    vfiles = _collect_verilog_files(
        file_loc=args.file_loc,
        file_list=args.lfile,
        verilog_files=args.verilog_files,
        extension=args.extension,
    )
    if not vfiles:
        parser.error("No Verilog files found. Use -f, -F, or positional file paths.")

    targets = _get_targets(args.targets) if args.targets else []
    if args.assertion_coi and targets:
        parser.error("Do not use --targets with --assertion-coi.")

    if args.assertion_coi:
        assertion_groups, assertion_targets = extract_assertion_targets(
            vfiles, assertion_file=args.assertion_file
        )
        if not assertion_targets:
            parser.error("No assertions found to extract COI targets.")
        targets = assertion_targets

    result = extract_coi(
        vfiles,
        top_module=args.top,
        targets=targets,
        include_dirs=args.include,
        clocks=args.clock,
        temporal_depth=args.temporal_depth,
        strip_assertions=args.assertion_coi,
        prefer_slang=not args.no_slang,
    )

    if args.list_targets:
        tlist = result["elaborate_info"][result["top_module"]]["targets"]
        for t in sorted(tlist):
            print(t)
        return

    cones = result["cones"]
    target_map = result["target_map"]

    if target_map:
        for orig, resolved in target_map.items():
            if isinstance(resolved, (list, tuple, set)):
                resolved_text = ", ".join(sorted(resolved))
            else:
                resolved_text = str(resolved)
            print("Resolved target '%s' -> '%s'" % (orig, resolved_text))

    if args.assertion_coi:
        assertion_groups, _ = extract_assertion_targets(
            vfiles, assertion_file=args.assertion_file
        )
        state_vars = collect_state_vars(
            result["elaborate_info"], result["top_module"], result["scope_module_map"]
        )
        for label, group_targets in assertion_groups:
            resolved = []
            for t in group_targets:
                mapped = target_map.get(t, t)
                if isinstance(mapped, (list, tuple, set)):
                    resolved.extend(mapped)
                else:
                    resolved.append(mapped)
            merged = merge_cones(cones, resolved)
            if args.print_a1:
                a1, kept, depth = compute_a1_for_targets(
                    result["dep_g"],
                    resolved,
                    state_vars,
                    depth=args.a1_depth,
                    max_state=args.a1_max_state,
                )
                if depth is None:
                    print("Assertion %s: A1 empty (no state vars in COI)" % label)
                else:
                    print(
                        "Assertion %s: A1 depth %d, %d state vars, kept %d nodes"
                        % (label, depth, len(a1), len(kept))
                    )
                    for node in sorted(a1):
                        print(node)
            print(
                "Assertion %s: %d targets, %d nodes, %d edges"
                % (label, len(resolved), len(merged.nodes()), len(merged.edges()))
            )
            if args.print_nodes:
                for node in sorted(merged.nodes()):
                    print(node)
            if args.print_edges:
                for src, dst in merged.edges():
                    print("%s -> %s" % (src, dst))
        return

    for target in result["resolved_targets"]:
        cone = cones.get(target)
        if not cone:
            print("No COI found for target: %s" % target)
            continue
        print("Target %s: %d nodes, %d edges" % (target, len(cone.nodes()), len(cone.edges())))
        if args.print_nodes:
            for node in sorted(cone.nodes()):
                print(node)
        if args.print_edges:
            for src, dst in cone.edges():
                print("%s -> %s" % (src, dst))

    if args.merge_targets and result["resolved_targets"]:
        merged = merge_cones(cones, result["resolved_targets"])
        print(
            "Merged COI: %d nodes, %d edges"
            % (len(merged.nodes()), len(merged.edges()))
        )
        if args.print_nodes:
            for node in sorted(merged.nodes()):
                print(node)
        if args.print_edges:
            for src, dst in merged.edges():
                print("%s -> %s" % (src, dst))


if __name__ == "__main__":
    main()
