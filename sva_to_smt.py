#!/usr/bin/env python3
import math
import re


class Token:
    def __init__(self, kind, value):
        self.kind = kind
        self.value = value

    def __repr__(self):
        return f"Token({self.kind}, {self.value})"


TOKEN_SPEC = [
    ("WS", r"\s+"),
    ("ARROW_OVERLAP", r"\|\-\>"),
    ("ARROW_NONOVERLAP", r"\|\=\>"),
    ("DELAY", r"\#\#"),
    ("LOGIC_AND", r"\&\&"),
    ("LOGIC_OR", r"\|\|"),
    ("EQ", r"=="),
    ("NEQ", r"!="),
    ("LE", r"<="),
    ("GE", r">="),
    ("LT", r"<"),
    ("GT", r">"),
    ("BIT_AND", r"\&"),
    ("BIT_OR", r"\|"),
    ("BIT_XOR", r"\^"),
    ("NOT", r"!"),
    ("LBRACK", r"\["),
    ("RBRACK", r"\]"),
    ("LPAREN", r"\("),
    ("RPAREN", r"\)"),
    ("COLON", r":"),
    ("COMMA", r","),
    ("STAR", r"\*"),
    ("BINARY", r"\d+'[bB][01xzXZ]+"),
    ("NUMBER", r"\d+"),
    ("THROUGHOUT", r"\bthroughout\b"),
    ("SYSDOL", r"\$[A-Za-z_][A-Za-z0-9_]*"),
    ("IDENT", r"[A-Za-z_][A-Za-z0-9_$.]*"),
]

TOKEN_RE = re.compile("|".join("(?P<%s>%s)" % pair for pair in TOKEN_SPEC))


def tokenize(text):
    tokens = []
    for match in TOKEN_RE.finditer(text):
        kind = match.lastgroup
        value = match.group()
        if kind == "WS":
            continue
        tokens.append(Token(kind, value))
    return tokens


def _strip_sv_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.DOTALL)
    text = re.sub(r"//.*", " ", text)
    return text


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


def _strip_assert_wrapper(text):
    stripped = _strip_sv_comments(text).strip()
    match = re.search(r"\bassert\s+property\b", stripped)
    if match:
        paren_idx = stripped.find("(", match.end())
        if paren_idx != -1:
            inner, _ = _extract_balanced_parens(stripped, paren_idx)
            if inner:
                stripped = inner.strip()
    return stripped


def _split_disable_iff(text):
    match = re.search(r"\bdisable\s+iff\b", text)
    if not match:
        return text.strip(), None
    paren_idx = text.find("(", match.end())
    if paren_idx == -1:
        raise ParseError("disable iff missing condition")
    cond, end_idx = _extract_balanced_parens(text, paren_idx)
    if not cond:
        raise ParseError("disable iff missing condition")
    remaining = (text[:match.start()] + text[end_idx:]).strip()
    return remaining, cond.strip()


class ParseError(Exception):
    pass


class BoolExpr:
    def to_smt(self, time, ctx):
        raise NotImplementedError()


class BoolConst(BoolExpr):
    def __init__(self, value):
        self.value = value

    def to_smt(self, time, ctx):
        return ("true" if self.value else "false"), ("Bool", None)


class BitVecConst(BoolExpr):
    def __init__(self, width, bits):
        self.width = width
        self.bits = bits

    def to_smt(self, time, ctx):
        return "#b" + self.bits, ("BV", self.width)


class NumConst(BoolExpr):
    def __init__(self, value):
        self.value = value

    def to_smt(self, time, ctx):
        if self.value in (0, 1):
            return ("true" if self.value == 1 else "false"), ("Bool", None)
        width = max(1, self.value.bit_length())
        bits = format(self.value, "b").zfill(width)
        return "#b" + bits, ("BV", width)


class Identifier(BoolExpr):
    def __init__(self, name):
        self.name = name

    def to_smt(self, time, ctx):
        if self.name not in ctx.signal_map:
            raise ParseError("Signal not found in SMT2 model: %s" % self.name)
        width = ctx.signal_widths.get(self.name, 1)
        expr = "(%s s%d)" % (ctx.signal_map[self.name], time)
        if width == 1:
            return expr, ("Bool", None)
        return expr, ("BV", width)


class BitSelect(BoolExpr):
    def __init__(self, var, idx):
        self.var = var
        self.idx = idx

    def to_smt(self, time, ctx):
        var_expr, var_type = self.var.to_smt(time, ctx)
        bit_expr = "((_ extract {0} {0}) {1})".format(
            self.idx, _cast_to_bv(var_expr, var_type)
        )
        return "(= %s #b1)" % bit_expr, ("Bool", None)


class RangeSelect(BoolExpr):
    def __init__(self, var, left, right):
        self.var = var
        self.left = left
        self.right = right

    def to_smt(self, time, ctx):
        var_expr, var_type = self.var.to_smt(time, ctx)
        left = max(self.left, self.right)
        right = min(self.left, self.right)
        expr = "((_ extract {0} {1}) {2})".format(
            left, right, _cast_to_bv(var_expr, var_type)
        )
        return expr, ("BV", left - right + 1)


class Not(BoolExpr):
    def __init__(self, expr):
        self.expr = expr

    def to_smt(self, time, ctx):
        val = self.expr.to_smt(time, ctx)
        if val is None:
            return None
        expr, typ = val
        expr = _cast_to_bool(expr, typ)
        return "(not %s)" % expr, ("Bool", None)


class BinaryOp(BoolExpr):
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

    def to_smt(self, time, ctx):
        left = self.left.to_smt(time, ctx)
        right = self.right.to_smt(time, ctx)
        if left is None or right is None:
            return None
        lexpr, ltype = left
        rexpr, rtype = right
        if self.op in ("&&", "||"):
            lexpr = _cast_to_bool(lexpr, ltype)
            rexpr = _cast_to_bool(rexpr, rtype)
            op = "and" if self.op == "&&" else "or"
            return "(%s %s %s)" % (op, lexpr, rexpr), ("Bool", None)
        if self.op in ("&", "|", "^"):
            if ltype[0] == "Bool" and rtype[0] == "Bool":
                op = {"&": "and", "|": "or", "^": "xor"}[self.op]
                return "(%s %s %s)" % (op, lexpr, rexpr), ("Bool", None)
            width = max(_bv_width(ltype), _bv_width(rtype))
            lexpr = _coerce_bv(lexpr, ltype, width)
            rexpr = _coerce_bv(rexpr, rtype, width)
            op = {"&": "bvand", "|": "bvor", "^": "bvxor"}[self.op]
            return "(%s %s %s)" % (op, lexpr, rexpr), ("BV", width)
        raise ParseError("Unsupported binary op: %s" % self.op)


class CompareOp(BoolExpr):
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

    def to_smt(self, time, ctx):
        left = self.left.to_smt(time, ctx)
        right = self.right.to_smt(time, ctx)
        if left is None or right is None:
            return None
        lexpr, ltype = left
        rexpr, rtype = right
        if self.op in ("==", "!="):
            if ltype[0] == "Bool" and rtype[0] == "Bool":
                if self.op == "==":
                    return "(= %s %s)" % (lexpr, rexpr), ("Bool", None)
                return "(distinct %s %s)" % (lexpr, rexpr), ("Bool", None)
            width = max(_bv_width(ltype), _bv_width(rtype))
            lexpr = _coerce_bv(lexpr, ltype, width)
            rexpr = _coerce_bv(rexpr, rtype, width)
            op = "=" if self.op == "==" else "distinct"
            return "(%s %s %s)" % (op, lexpr, rexpr), ("Bool", None)
        width = max(_bv_width(ltype), _bv_width(rtype))
        lexpr = _coerce_bv(lexpr, ltype, width)
        rexpr = _coerce_bv(rexpr, rtype, width)
        op = {
            "<": "bvult",
            "<=": "bvule",
            ">": "bvugt",
            ">=": "bvuge",
        }[self.op]
        return "(%s %s %s)" % (op, lexpr, rexpr), ("Bool", None)


class Past(BoolExpr):
    def __init__(self, expr, delay, default=None):
        self.expr = expr
        self.delay = delay
        self.default = default

    def to_smt(self, time, ctx):
        target = time - self.delay
        if target < 0:
            if self.default is None:
                return None
            return self.default.to_smt(0, ctx)
        return self.expr.to_smt(target, ctx)


class Stable(BoolExpr):
    def __init__(self, expr):
        self.expr = expr

    def to_smt(self, time, ctx):
        cur = self.expr.to_smt(time, ctx)
        prev = Past(self.expr, 1).to_smt(time, ctx)
        if cur is None or prev is None:
            return None
        cur_expr, cur_type = cur
        prev_expr, prev_type = prev
        cur_expr = _cast_to_bv(cur_expr, cur_type)
        prev_expr = _cast_to_bv(prev_expr, prev_type)
        return "(= %s %s)" % (prev_expr, cur_expr), ("Bool", None)


class Rose(BoolExpr):
    def __init__(self, expr):
        self.expr = expr

    def to_smt(self, time, ctx):
        cur = self.expr.to_smt(time, ctx)
        prev = Past(self.expr, 1).to_smt(time, ctx)
        if cur is None or prev is None:
            return None
        cur_expr, cur_type = cur
        prev_expr, prev_type = prev
        cur_expr = _cast_to_bool(cur_expr, cur_type)
        prev_expr = _cast_to_bool(prev_expr, prev_type)
        return "(and (not %s) %s)" % (prev_expr, cur_expr), ("Bool", None)


class Fell(BoolExpr):
    def __init__(self, expr):
        self.expr = expr

    def to_smt(self, time, ctx):
        cur = self.expr.to_smt(time, ctx)
        prev = Past(self.expr, 1).to_smt(time, ctx)
        if cur is None or prev is None:
            return None
        cur_expr, cur_type = cur
        prev_expr, prev_type = prev
        cur_expr = _cast_to_bool(cur_expr, cur_type)
        prev_expr = _cast_to_bool(prev_expr, prev_type)
        return "(and %s (not %s))" % (prev_expr, cur_expr), ("Bool", None)


class OneHot0(BoolExpr):
    def __init__(self, expr):
        self.expr = expr

    def to_smt(self, time, ctx):
        cur = self.expr.to_smt(time, ctx)
        if cur is None:
            return None
        cur_expr, cur_type = cur
        width = _bv_width(cur_type)
        if width <= 1:
            return "true", ("Bool", None)
        cur_expr = _cast_to_bv(cur_expr, cur_type)
        zero = "#b" + ("0" * width)
        one = "#b" + ("0" * (width - 1) + "1")
        check = "(= (bvand {0} (bvsub {0} {1})) {2})".format(cur_expr, one, zero)
        return "(or (= {0} {1}) {2})".format(cur_expr, zero, check), ("Bool", None)


class OneHot(BoolExpr):
    def __init__(self, expr):
        self.expr = expr

    def to_smt(self, time, ctx):
        cur = self.expr.to_smt(time, ctx)
        if cur is None:
            return None
        cur_expr, cur_type = cur
        width = _bv_width(cur_type)
        if width <= 1:
            # 单比特：必须是 1
            return _cast_to_bool(cur_expr, cur_type), ("Bool", None)
        cur_expr = _cast_to_bv(cur_expr, cur_type)
        zero = "#b" + ("0" * width)
        one = "#b" + ("0" * (width - 1) + "1")
        # x != 0 && (x & (x-1)) == 0
        not_zero = "(distinct {0} {1})".format(cur_expr, zero)
        is_power_of_two = "(= (bvand {0} (bvsub {0} {1})) {2})".format(cur_expr, one, zero)
        return "(and {0} {1})".format(not_zero, is_power_of_two), ("Bool", None)


class Changed(BoolExpr):
    def __init__(self, expr):
        self.expr = expr

    def to_smt(self, time, ctx):
        # 当前值
        cur = self.expr.to_smt(time, ctx)
        # 上一周期的值
        prev = Past(self.expr, 1).to_smt(time, ctx)
        if cur is None or prev is None:
            return None
        cur_expr, cur_type = cur
        prev_expr, prev_type = prev
        # 转换为位向量进行比较
        cur_expr = _cast_to_bv(cur_expr, cur_type)
        prev_expr = _cast_to_bv(prev_expr, prev_type)
        # 不相等
        return "(distinct {0} {1})".format(prev_expr, cur_expr), ("Bool", None)


class Sequence:
    def matches(self, start, ctx):
        raise NotImplementedError()

    def has_unbounded(self):
        return False

    def max_span(self):
        return 0


class SeqBool(Sequence):
    def __init__(self, expr):
        self.expr = expr

    def matches(self, start, ctx):
        val = self.expr.to_smt(start, ctx)
        if val is None:
            return []
        expr, typ = val
        expr = _cast_to_bool(expr, typ)
        return [(expr, start, start)]

    def max_span(self):
        return 0


class SeqDelay(Sequence):
    def __init__(self, left, delay_range, right):
        self.left = left
        self.delay_range = delay_range
        self.right = right

    def matches(self, start, ctx):
        results = []
        for cond_l, s_l, e_l in self.left.matches(start, ctx):
            for delay in self.delay_range.values(ctx.max_time - e_l):
                start_r = e_l + delay
                if start_r > ctx.max_time:
                    continue
                for cond_r, s_r, e_r in self.right.matches(start_r, ctx):
                    results.append(("(and %s %s)" % (cond_l, cond_r), s_l, e_r))
        return results

    def has_unbounded(self):
        return self.left.has_unbounded() or self.right.has_unbounded()

    def max_span(self):
        left_span = self.left.max_span()
        right_span = self.right.max_span()
        max_delay = self.delay_range.max_delay()
        if max_delay is None or left_span is None or right_span is None:
            return None
        return left_span + max_delay + right_span


class SeqRepeat(Sequence):
    def __init__(self, seq, min_rep, max_rep):
        self.seq = seq
        self.min_rep = min_rep
        self.max_rep = max_rep

    def matches(self, start, ctx):
        results = []
        max_rep = self.max_rep
        if max_rep is None:
            max_rep = _safe_repeat_upper(self.seq, start, ctx.max_time)
        for reps in range(self.min_rep, max_rep + 1):
            results.extend(_repeat_exact(self.seq, start, reps, ctx))
        return results

    def has_unbounded(self):
        return self.max_rep is None or self.seq.has_unbounded()

    def max_span(self):
        span = self.seq.max_span()
        if span is None or self.max_rep is None:
            return None
        if self.max_rep == 0:
            return 0
        return self.max_rep * (span + 1) - 1


class SeqThroughout(Sequence):
    def __init__(self, cond_expr, seq):
        self.cond_expr = cond_expr
        self.seq = seq

    def matches(self, start, ctx):
        results = []
        for cond_s, s_s, e_s in self.seq.matches(start, ctx):
            guards = []
            for t in range(s_s, e_s + 1):
                val = self.cond_expr.to_smt(t, ctx)
                if val is None:
                    guards = None
                    break
                gexpr, gtype = val
                guards.append(_cast_to_bool(gexpr, gtype))
            if guards is None:
                continue
            guard_expr = "true" if not guards else "(and %s)" % " ".join(guards)
            results.append(("(and %s %s)" % (cond_s, guard_expr), s_s, e_s))
        return results

    def has_unbounded(self):
        return self.seq.has_unbounded()

    def max_span(self):
        return self.seq.max_span()


class DelayRange:
    def __init__(self, min_delay, max_delay):
        self.min_delay = min_delay
        self.max_delay_value = max_delay

    def values(self, max_allowed):
        if self.max_delay_value is None:
            return list(range(self.min_delay, max_allowed + 1))
        return list(range(self.min_delay, min(self.max_delay_value, max_allowed) + 1))

    def max_delay(self):
        return self.max_delay_value


class Property:
    def __init__(self, antecedent, op, consequent):
        self.antecedent = antecedent
        self.op = op
        self.consequent = consequent


class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        if self.pos >= len(self.tokens):
            return None
        return self.tokens[self.pos]

    def consume(self, kind=None):
        token = self.peek()
        if token is None:
            return None
        if kind and token.kind != kind:
            raise ParseError("Expected %s but got %s" % (kind, token.kind))
        self.pos += 1
        return token

    def parse_property(self):
        seq = self.parse_sequence()
        token = self.peek()
        if token and token.kind in ("ARROW_OVERLAP", "ARROW_NONOVERLAP"):
            op = self.consume().kind
            rhs = self.parse_sequence()
            return Property(seq, op, rhs)
        return Property(seq, None, None)

    def parse_sequence(self):
        if self.peek() and self.peek().kind == "DELAY":
            seq = SeqBool(BoolConst(True))
        else:
            seq = self.parse_seq_atom()
        while True:
            token = self.peek()
            if token is None:
                break
            if token.kind == "DELAY":
                self.consume()
                delay_range = self.parse_delay_range()
                rhs = self.parse_seq_atom()
                seq = SeqDelay(seq, delay_range, rhs)
                continue
            if token.kind == "THROUGHOUT":
                self.consume()
                rhs = self.parse_seq_atom()
                if not isinstance(seq, SeqBool):
                    raise ParseError("Left of throughout must be boolean expression")
                seq = SeqThroughout(seq.expr, rhs)
                continue
            break
        return seq

    def parse_delay_range(self):
        token = self.peek()
        if token.kind == "LBRACK":
            self.consume("LBRACK")
            min_delay = int(self.consume("NUMBER").value)
            self.consume("COLON")
            max_delay = int(self.consume("NUMBER").value)
            self.consume("RBRACK")
            return DelayRange(min_delay, max_delay)
        value = int(self.consume("NUMBER").value)
        return DelayRange(value, value)

    def parse_seq_atom(self):
        if self.peek() and self.peek().kind == "LPAREN":
            save_pos = self.pos
            self.consume("LPAREN")
            try:
                expr = self.parse_expr()
                self.consume("RPAREN")
                seq = SeqBool(expr)
            except ParseError:
                self.pos = save_pos
                self.consume("LPAREN")
                seq = self.parse_sequence()
                self.consume("RPAREN")
        else:
            expr = self.parse_expr()
            seq = SeqBool(expr)
        seq = self.parse_repeat(seq)
        return seq

    def parse_repeat(self, seq):
        token = self.peek()
        if token and token.kind == "LBRACK":
            save_pos = self.pos
            self.consume("LBRACK")
            if self.peek() and self.peek().kind == "STAR":
                self.consume("STAR")
                if self.peek() and self.peek().kind == "RBRACK":
                    self.consume("RBRACK")
                    return SeqRepeat(seq, 0, None)
                if self.peek() and self.peek().kind == "NUMBER":
                    min_rep = int(self.consume("NUMBER").value)
                    max_rep = min_rep
                    if self.peek() and self.peek().kind == "COLON":
                        self.consume("COLON")
                        max_rep = int(self.consume("NUMBER").value)
                    self.consume("RBRACK")
                    return SeqRepeat(seq, min_rep, max_rep)
            self.pos = save_pos
        return seq

    def parse_expr(self):
        return self.parse_or()

    def parse_or(self):
        expr = self.parse_xor()
        while self.peek() and self.peek().kind in ("LOGIC_OR", "BIT_OR"):
            op = self.consume().value
            expr = BinaryOp("||" if op == "||" else "|", expr, self.parse_xor())
        return expr

    def parse_xor(self):
        expr = self.parse_and()
        while self.peek() and self.peek().kind == "BIT_XOR":
            self.consume()
            expr = BinaryOp("^", expr, self.parse_and())
        return expr

    def parse_and(self):
        expr = self.parse_compare()
        while self.peek() and self.peek().kind in ("LOGIC_AND", "BIT_AND"):
            op = self.consume().value
            expr = BinaryOp("&&" if op == "&&" else "&", expr, self.parse_compare())
        return expr

    def parse_compare(self):
        expr = self.parse_unary()
        token = self.peek()
        if token and token.kind in ("EQ", "NEQ", "LT", "LE", "GT", "GE"):
            op = self.consume().value
            expr = CompareOp(op, expr, self.parse_unary())
        return expr

    def parse_unary(self):
        token = self.peek()
        if token and token.kind == "NOT":
            self.consume()
            return Not(self.parse_unary())
        return self.parse_primary()

    def parse_primary(self):
        token = self.peek()
        if token is None:
            raise ParseError("Unexpected end of input")
        if token.kind == "LPAREN":
            self.consume("LPAREN")
            expr = self.parse_expr()
            self.consume("RPAREN")
            return expr
        if token.kind == "SYSDOL":
            return self.parse_sysfunc()
        if token.kind == "BINARY":
            tok = self.consume()
            width, bits = tok.value.split("'b")
            return BitVecConst(int(width), bits.lower())
        if token.kind == "NUMBER":
            return NumConst(int(self.consume().value))
        if token.kind == "IDENT":
            return self.parse_identifier()
        raise ParseError("Unexpected token: %s" % token.kind)

    def parse_identifier(self):
        ident = Identifier(self.consume("IDENT").value)
        if self.peek() and self.peek().kind == "LBRACK":
            next_tok = self.tokens[self.pos + 1] if self.pos + 1 < len(self.tokens) else None
            if next_tok and next_tok.kind == "STAR":
                return ident
            self.consume("LBRACK")
            left = int(self.consume("NUMBER").value)
            if self.peek() and self.peek().kind == "COLON":
                self.consume("COLON")
                right = int(self.consume("NUMBER").value)
                self.consume("RBRACK")
                return RangeSelect(ident, left, right)
            self.consume("RBRACK")
            return BitSelect(ident, left)
        return ident

    def parse_sysfunc(self):
        name = self.consume("SYSDOL").value
        self.consume("LPAREN")
        args = [self.parse_expr()]
        while self.peek() and self.peek().kind == "COMMA":
            self.consume()
            args.append(self.parse_expr())
        self.consume("RPAREN")
        if name == "$past":
            delay = 1
            default = None
            if len(args) >= 2:
                if not isinstance(args[1], NumConst):
                    raise ParseError("$past delay must be constant")
                delay = args[1].value
            if len(args) == 3:
                default = args[2]
            return Past(args[0], delay, default)
        if name == "$stable":
            return Stable(args[0])
        if name == "$rose":
            return Rose(args[0])
        if name == "$fell":
            return Fell(args[0])
        if name == "$onehot0":
            return OneHot0(args[0])
        if name == "$onehot":
            return OneHot(args[0])
        if name == "$changed":
            return Changed(args[0])
        if name == "$isunknown":
            raise ParseError(
                "$isunknown is not supported: SMT2 model uses 2-value logic (no X/Z). "
                "Use simulation tools for X/Z detection."
            )
        raise ParseError("Unsupported system function: %s" % name)


def _bv_width(typ):
    if typ[0] == "Bool":
        return 1
    return typ[1]


def _cast_to_bool(expr, typ):
    if typ[0] == "Bool":
        return expr
    width = typ[1]
    zero = "#b" + ("0" * width)
    return "(distinct %s %s)" % (expr, zero)


def _cast_to_bv(expr, typ):
    if typ[0] == "BV":
        return expr
    return "(ite %s #b1 #b0)" % expr


def _coerce_bv(expr, typ, width):
    expr = _cast_to_bv(expr, typ)
    cur_width = _bv_width(typ)
    if cur_width == width:
        return expr
    if cur_width > width:
        return "(_ extract %d 0 (%s))" % (width - 1, expr)
    return "((_ zero_extend %d) %s)" % (width - cur_width, expr)


def _repeat_exact(seq, start, reps, ctx):
    if reps == 0:
        return [("true", start, start - 1)]
    results = []
    for cond_s, s_s, e_s in seq.matches(start, ctx):
        if e_s > ctx.max_time:
            continue
        for cond_r, s_r, e_r in _repeat_exact(seq, e_s + 1, reps - 1, ctx):
            if e_r > ctx.max_time:
                continue
            if cond_r == "true":
                cond = cond_s
            else:
                cond = "(and %s %s)" % (cond_s, cond_r)
            results.append((cond, s_s, e_r))
    return results


def _safe_repeat_upper(seq, start, max_time):
    span = seq.max_span()
    if span is None:
        return max_time - start + 1
    if span == 0:
        return max_time - start + 1
    return max(0, (max_time - start + 1) // (span + 1))


class Context:
    def __init__(self, signal_map, signal_widths, max_time):
        self.signal_map = signal_map
        self.signal_widths = signal_widths
        self.max_time = max_time


def _disable_guard_expr(disable_expr, start, end, ctx):
    if disable_expr is None:
        return "true"
    guards = []
    for t in range(start, end + 1):
        val = disable_expr.to_smt(t, ctx)
        if val is None:
            return None
        expr, typ = val
        guards.append("(not %s)" % _cast_to_bool(expr, typ))
    if not guards:
        return "true"
    if len(guards) == 1:
        return guards[0]
    return "(and %s)" % " ".join(guards)


def _extract_signal_widths(smt2_text):
    widths = {}
    for line in smt2_text.splitlines():
        if line.startswith("; yosys-smt2-"):
            parts = line.split()
            if len(parts) >= 4 and parts[1] in ("yosys-smt2-input", "yosys-smt2-output", "yosys-smt2-wire", "yosys-smt2-register"):
                name = parts[2]
                try:
                    width = int(parts[3])
                except ValueError:
                    continue
                widths[name] = width
    return widths


def _max_span_from_seq(seq):
    return seq.max_span()


def translate_sva_property(
    assertion_expr,
    smt2_text,
    top_module,
    signal_map,
    max_time=None,
    start_time=1,
):
    stripped = _strip_assert_wrapper(assertion_expr)
    stripped = re.sub(r"@\s*\([^)]*\)", "", stripped).strip()
    stripped, disable_expr = _split_disable_iff(stripped)
    tokens = tokenize(stripped)
    parser = Parser(tokens)
    prop = parser.parse_property()
    if parser.peek() is not None:
        raise ParseError("Unexpected tokens at end of property")
    disable_ast = None
    if disable_expr:
        dparser = Parser(tokenize(disable_expr))
        disable_ast = dparser.parse_expr()
        if dparser.peek() is not None:
            raise ParseError("Unexpected tokens at end of disable iff expression")
    widths = _extract_signal_widths(smt2_text)
    if max_time is None:
        max_span = _max_span_from_seq(prop.antecedent)
        if prop.consequent is not None:
            max_span_c = _max_span_from_seq(prop.consequent)
            if max_span is None or max_span_c is None:
                max_span = None
            else:
                max_span = max(max_span, max_span_c)
        if max_span is None:
            raise ParseError("Unbounded sequence, please set max_time")
        max_time = max_span
    ctx = Context(signal_map, widths, max_time)

    violations = []
    if start_time < 0:
        start_time = 0
    for start in range(start_time, max_time + 1):
        antecedent_matches = prop.antecedent.matches(start, ctx)
        if not antecedent_matches:
            continue
        for cond_a, s_a, e_a in antecedent_matches:
            if e_a < 0:
                continue
            cons_start = e_a if prop.op == "ARROW_OVERLAP" else e_a + 1
            if prop.op is None:
                guard = _disable_guard_expr(disable_ast, s_a, e_a, ctx)
                if guard is None:
                    continue
                if guard == "true":
                    violation = "(not %s)" % cond_a
                else:
                    violation = "(and %s (not %s))" % (guard, cond_a)
                violations.append(violation)
                continue
            if cons_start < 0 or cons_start > max_time:
                continue
            cons_matches = prop.consequent.matches(cons_start, ctx)
            if not cons_matches:
                continue
            guarded = []
            guards = []
            for cond, _, e_r in cons_matches:
                guard = _disable_guard_expr(disable_ast, s_a, e_r, ctx)
                if guard is None:
                    continue
                guards.append(guard)
                if guard == "true":
                    guarded.append(cond)
                else:
                    guarded.append("(and %s %s)" % (guard, cond))
            if not guarded:
                continue
            cons_expr = guarded[0] if len(guarded) == 1 else "(or %s)" % " ".join(guarded)
            if disable_ast is None:
                violation = "(and %s (not %s))" % (cond_a, cons_expr)
            else:
                any_guard = guards[0] if len(guards) == 1 else "(or %s)" % " ".join(guards)
                if any_guard == "true":
                    violation = "(and %s (not %s))" % (cond_a, cons_expr)
                else:
                    violation = "(and %s %s (not %s))" % (cond_a, any_guard, cons_expr)
            violations.append(violation)

    if not violations:
        violation_expr = "false"
    elif len(violations) == 1:
        violation_expr = violations[0]
    else:
        violation_expr = "(or %s)" % " ".join(violations)
    return violation_expr, max_time
