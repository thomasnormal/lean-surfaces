#!/usr/bin/env python3.12
"""SystemVerilog -> standardized AST envelope extractor for the lean_models
SV lane (M0 tier, see docs/sv-design-m0.md).

Usage (run from the repo root):

    python3.12 extractors/sv/extract.py <file.sv> [more.sv ...]

For each source file ``foo.sv`` this writes ``foo.sv.json`` next to the
source: the envelope described in docs/sv-envelope-schema.md
(schema "sv-0.1").

Guarantees:
  * Never fails on valid SystemVerilog — anything outside the M0 node
    vocabulary becomes an ``Unsupported`` node (slang class name + source
    text, <= 200 chars).
  * Deterministic: same input bytes (and same pyslang version) => same
    output bytes. json indent=2; fixed key order: "kind" first, then
    "span", then the node's fields in the order documented in
    docs/sv-envelope-schema.md.
  * Widths are ELABORATED widths from pyslang's compilation (e.g. the
    unbased unsized literal '0 in an 8-bit context is emitted as an
    8-bit Literal).
  * Hard errors (non-zero exit, no output): unreadable file / not UTF-8.

Requires python3.12 + pyslang 11.x.
"""

import argparse
import hashlib
import json
import os
import sys

import pyslang
from pyslang.ast import (
    BinaryOperator,
    Compilation,
    ConversionKind,
    EdgeKind,
    ProceduralBlockKind,
    StatementBlockKind,
    UnaryOperator,
    UniquePriorityCheck,
)
from pyslang.syntax import SyntaxTree

SCHEMA_VERSION = "sv-0.1"
FRONTEND = {"name": "pyslang", "version": pyslang.__version__}

UNSUPPORTED_TEXT_LIMIT = 200

# Operator maps: slang enum -> the surface symbol emitted in the envelope.
# Anything not listed makes the containing node Unsupported.
BINARY_OPS = {
    BinaryOperator.Add: "+",
    BinaryOperator.Subtract: "-",
    BinaryOperator.BinaryAnd: "&",
    BinaryOperator.BinaryOr: "|",
    BinaryOperator.BinaryXor: "^",
    BinaryOperator.Equality: "==",
    BinaryOperator.Inequality: "!=",
    BinaryOperator.LessThan: "<",
    BinaryOperator.LessThanEqual: "<=",
    BinaryOperator.GreaterThan: ">",
    BinaryOperator.GreaterThanEqual: ">=",
    # Self-check tier (docs/sv-corpus-coverage.md §f): case equality and
    # short-circuit-free logical ops. All four yield 1-bit results.
    BinaryOperator.CaseEquality: "===",
    BinaryOperator.CaseInequality: "!==",
    BinaryOperator.LogicalAnd: "&&",
    BinaryOperator.LogicalOr: "||",
}
COMPARISON_SYMS = ("==", "!=", "<", "<=", ">", ">=", "===", "!==")
LOGICAL_SYMS = ("&&", "||")
# Order comparisons are SIGNED iff both operand types are signed (LRM
# §11.8.1). The envelope spells those "s<" etc.; the self-check evaluator
# implements two's-complement comparison (closing the census's signedness
# gap loudly instead of mis-evaluating).
ORDER_CMP_SYMS = ("<", "<=", ">", ">=")
# System tasks of the self-check tier (statement position only).
SYSCALL_FMT = ("$display", "$write")
SYSCALL_CTRL = ("$finish", "$stop")
UNARY_OPS = {
    UnaryOperator.BitwiseNot: "~",
    UnaryOperator.LogicalNot: "!",
    UnaryOperator.Minus: "-",
}


class ExtractError(Exception):
    """Fatal extractor error (message to stderr, exit code 1)."""


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------

def range_span(sm, sr):
    """Span dict from a slang SourceRange (1-based lines/cols, end exclusive),
    or None when unavailable."""
    if sr is None:
        return None
    try:
        return {
            "line": sm.getLineNumber(sr.start),
            "col": sm.getColumnNumber(sr.start),
            "end_line": sm.getLineNumber(sr.end),
            "end_col": sm.getColumnNumber(sr.end),
        }
    except Exception:
        return None


def node_span(sm, node):
    """Best-effort span for an AST statement/expression/timing control."""
    return range_span(sm, getattr(node, "sourceRange", None))


def sym_span(sm, sym):
    """Best-effort span for a symbol: its syntax node's range, else a point
    span at its location, else None."""
    syn = getattr(sym, "syntax", None)
    if syn is not None:
        sp = range_span(sm, getattr(syn, "sourceRange", None))
        if sp is not None:
            return sp
    loc = getattr(sym, "location", None)
    if loc is not None:
        try:
            line = sm.getLineNumber(loc)
            col = sm.getColumnNumber(loc)
            return {"line": line, "col": col, "end_line": line, "end_col": col}
        except Exception:
            return None
    return None


# Raw bytes of the file currently being extracted (set by process_file);
# used to recover exact source text for Unsupported nodes. slang source
# offsets are byte offsets into the file content.
_SOURCE_BYTES = None


def source_text(node):
    """Exact source text of a symbol/statement/expression (via its source
    range's byte offsets), truncated to UNSUPPORTED_TEXT_LIMIT chars.
    Empty string if unavailable."""
    syn = getattr(node, "syntax", None)
    holder = syn if syn is not None else node
    sr = getattr(holder, "sourceRange", None)
    if sr is not None and _SOURCE_BYTES is not None:
        try:
            s, e = sr.start.offset, sr.end.offset
            if 0 <= s <= e <= len(_SOURCE_BYTES):
                txt = _SOURCE_BYTES[s:e].decode("utf-8", errors="replace").strip()
                if txt:
                    return txt[:UNSUPPORTED_TEXT_LIMIT]
        except Exception:
            pass
    try:
        if syn is not None:
            return str(syn).strip()[:UNSUPPORTED_TEXT_LIMIT]
    except Exception:
        pass
    return ""


def unsupported(sm, node, sv_kind=None, text=None):
    return {
        "kind": "Unsupported",
        "span": sym_span(sm, node) if _is_symbol(node) else node_span(sm, node),
        "sv_kind": sv_kind if sv_kind is not None else type(node).__name__,
        "text": text if text is not None else source_text(node),
    }


def _is_symbol(node):
    # Symbols have .location and no .sourceRange of their own.
    return hasattr(node, "location") and not hasattr(node, "sourceRange")


def internal_error(exc):
    return {
        "kind": "Unsupported",
        "span": None,
        "sv_kind": "ExtractorInternal:" + type(exc).__name__,
        "text": str(exc)[:UNSUPPORTED_TEXT_LIMIT],
    }


def type_width(t):
    """(width, None) when t is an M0-supported type (unsigned 4-state scalar
    or [W-1:0] packed vector of a 4-state scalar), else (None, reason)."""
    try:
        if not t.isFourState:
            return None, "2state"
        if t.isSigned:
            return None, "signed"
        ct = t.canonicalType
        cname = type(ct).__name__
        if cname == "ScalarType":
            return 1, None
        if cname == "PackedArrayType":
            w = ct.bitWidth
            rng = ct.range
            elem = ct.elementType.canonicalType
            if (
                rng.left == w - 1
                and rng.right == 0
                and type(elem).__name__ == "ScalarType"
            ):
                return w, None
            return None, "range"
        return None, "type"
    except Exception:
        return None, "type"


def svint_bits(sv):
    """SVInt -> MSB-first string over {0,1,x,z}, length == bitWidth.
    (SVInt indexing is LSB-first: sv[0] is bit 0.)"""
    w = sv.bitWidth
    return "".join(str(sv[i]) for i in range(w - 1, -1, -1))


def type_width_2s(t):
    """Self-check-tier type check: `(width, two_state, None)` when `t` is an
    unsigned scalar or `[W-1:0]` packed vector of a scalar type — 4-state
    (`logic`/`reg`) or 2-state (`bit`) — else `(None, None, reason)`.
    Signed types (`int`, `integer`, `byte`, ...) stay out of the tier: the
    envelope carries no signedness, so admitting them would silently
    mis-evaluate order comparisons and `%d` (census robustness note 3)."""
    try:
        if t.isSigned:
            return None, None, "signed"
        ct = t.canonicalType
        cname = type(ct).__name__
        if cname == "ScalarType":
            return 1, (not t.isFourState), None
        if cname == "PackedArrayType":
            w = ct.bitWidth
            rng = ct.range
            elem = ct.elementType.canonicalType
            if (
                rng.left == w - 1
                and rng.right == 0
                and type(elem).__name__ == "ScalarType"
            ):
                return w, (not t.isFourState), None
            return None, None, "range"
        return None, None, "type"
    except Exception:
        return None, None, "type"


def squash2_wrap(d, width):
    """Wrap a converted RHS in a `Squash2` node (LRM §6.3.1: assigning a
    4-state value to a 2-state variable maps x/z bits to 0). Idempotent."""
    if d is None or d.get("kind") == "Squash2":
        return d
    return {"kind": "Squash2", "span": None, "width": width, "operand": d}


def const_literal(sm, e):
    """The `Literal` node for an expression slang already folded to an SVInt
    constant during binding (`e.constant`), else None. Never raises; never
    evaluates on demand (pyslang's EvalContext is crash-prone — only the
    binder-populated attribute is consulted)."""
    try:
        c = e.constant
        if c is None:
            return None
        sv = c.value
        if type(sv).__name__ != "SVInt":
            return None
        if sv.bitWidth != e.type.bitWidth:
            return None
        return {
            "kind": "Literal",
            "span": node_span(sm, e),
            "width": sv.bitWidth,
            "bits": svint_bits(sv),
        }
    except Exception:
        return None


def width_of(d):
    """Resolved width of a converted expression dict, or None (Unsupported)."""
    if d is None or d.get("kind") == "Unsupported":
        return None
    return d.get("width")


# ---------------------------------------------------------------------------
# Expressions
# ---------------------------------------------------------------------------

def convert_expr(sm, e):
    try:
        return _convert_expr(sm, e)
    except Exception as exc:  # never fail: broken node -> Unsupported
        return internal_error(exc)


def _convert_expr(sm, e):
    if e is None:
        return None
    if getattr(e, "bad", False):
        return unsupported(sm, e, "InvalidExpression")

    cname = type(e).__name__

    # Implicit/propagated conversions that do NOT change the width are
    # elaboration artifacts (2-state literal -> 4-state context, sign
    # reinterpretation); unwrap them transparently. A width-CHANGING
    # implicit conversion is exactly the "width mismatch in source" case
    # the M0 contract maps to Unsupported.
    if cname == "ConversionExpression":
        kind = e.conversionKind
        if kind in (ConversionKind.Implicit, ConversionKind.Propagated):
            ow, tw = e.operand.type.bitWidth, e.type.bitWidth
            state_squash = e.operand.type.isFourState and not e.type.isFourState
            if ow == tw:
                if state_squash:
                    # 4-state -> 2-state, same width: x/z |-> 0 (§6.3.1).
                    return {
                        "kind": "Squash2",
                        "span": node_span(sm, e),
                        "width": tw,
                        "operand": _convert_expr(sm, e.operand),
                    }
                return _convert_expr(sm, e.operand)
            # Width-changing implicit conversion (self-check tier §f):
            # 1. slang folded it to a constant -> emit the folded Literal
            #    (correct for signed operands too — slang applied the LRM).
            lit = const_literal(sm, e)
            if lit is not None:
                return lit
            # 2. unsigned integral operand -> Resize (zero-extend / keep
            #    low bits). Signed non-constant operands would need
            #    sign-extension the envelope cannot express -> Unsupported.
            try:
                resizable = (
                    e.operand.type.isIntegral
                    and e.type.isIntegral
                    and not e.operand.type.isSigned
                )
            except Exception:
                resizable = False
            if resizable:
                inner = _convert_expr(sm, e.operand)
                if state_squash:
                    inner = {
                        "kind": "Squash2",
                        "span": node_span(sm, e),
                        "width": ow,
                        "operand": inner,
                    }
                return {
                    "kind": "Resize",
                    "span": node_span(sm, e),
                    "width": tw,
                    "operand": inner,
                }
            return unsupported(sm, e, "ConversionExpression:width")
        return unsupported(sm, e, "ConversionExpression:" + str(kind).split(".")[-1])

    if cname == "NamedValueExpression":
        sym = e.symbol
        skind = str(sym.kind).split(".")[-1]
        if skind not in ("Variable", "Net"):
            return unsupported(sm, e, "NamedValueExpression:" + skind)
        w, _two, reason = type_width_2s(e.type)
        if w is None:
            # Keep the historical tag for 2-state-but-otherwise-bad types.
            if reason == "type" and not getattr(e.type, "isFourState", True):
                reason = "2state"
            return unsupported(sm, e, "NamedValueExpression:" + reason)
        return {
            "kind": "Ident",
            "span": node_span(sm, e),
            "width": w,
            "name": sym.name,
        }

    if cname in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
        sv = e.value
        return {
            "kind": "Literal",
            "span": node_span(sm, e),
            "width": sv.bitWidth,
            "bits": svint_bits(sv),
        }

    if cname == "StringLiteral":
        # LRM §11.10.1: a string literal is a constant number, one 8-bit
        # ASCII code per char, first char most significant; "" is 8'd0.
        try:
            data = e.value.encode("latin-1")
        except (UnicodeEncodeError, Exception):
            return unsupported(sm, e, "StringLiteral:encoding")
        w = e.type.bitWidth
        if w != (8 * len(data) if data else 8):
            return unsupported(sm, e, "StringLiteral:width")
        bits = "".join(format(b, "08b") for b in data) if data else "0" * 8
        return {
            "kind": "Literal",
            "span": node_span(sm, e),
            "width": w,
            "bits": bits,
        }

    if cname == "UnaryExpression":
        sym = UNARY_OPS.get(e.op)
        if sym is None:
            return unsupported(
                sm, e, "UnaryExpression:" + str(e.op).split(".")[-1]
            )
        operand = _convert_expr(sm, e.operand)
        myw = e.type.bitWidth
        ow = width_of(operand)
        ok = (myw == 1) if sym == "!" else (ow is None or ow == myw)
        if not ok:
            return unsupported(sm, e, "UnaryExpression:width")
        return {
            "kind": "Unary",
            "span": node_span(sm, e),
            "width": myw,
            "op": sym,
            "operand": operand,
        }

    if cname == "BinaryExpression":
        sym = BINARY_OPS.get(e.op)
        if sym is None:
            return unsupported(
                sm, e, "BinaryExpression:" + str(e.op).split(".")[-1]
            )
        left = _convert_expr(sm, e.left)
        right = _convert_expr(sm, e.right)
        myw = e.type.bitWidth
        lw, rw = width_of(left), width_of(right)
        if sym in COMPARISON_SYMS:
            ok = myw == 1 and (lw is None or rw is None or lw == rw)
        elif sym in LOGICAL_SYMS:
            # &&/||: operands are self-determined (any widths), result 1 bit.
            ok = myw == 1
        else:
            ok = (lw is None or lw == myw) and (rw is None or rw == myw)
        if not ok:
            return unsupported(sm, e, "BinaryExpression:width")
        if sym in ORDER_CMP_SYMS:
            try:
                if e.left.type.isSigned and e.right.type.isSigned:
                    sym = "s" + sym  # signed comparison (LRM §11.8.1)
            except Exception:
                return unsupported(sm, e, "BinaryExpression:signedness")
        return {
            "kind": "Binary",
            "span": node_span(sm, e),
            "width": myw,
            "op": sym,
            "left": left,
            "right": right,
        }

    if cname == "ConditionalExpression":
        conds = e.conditions
        if len(conds) != 1:
            return unsupported(sm, e, "ConditionalExpression:multi")
        if conds[0].pattern is not None:
            return unsupported(sm, e, "ConditionalExpression:pattern")
        cond = _convert_expr(sm, conds[0].expr)
        then = _convert_expr(sm, e.left)
        els = _convert_expr(sm, e.right)
        myw = e.type.bitWidth
        tw, ew = width_of(then), width_of(els)
        if (tw is not None and tw != myw) or (ew is not None and ew != myw):
            return unsupported(sm, e, "ConditionalExpression:width")
        return {
            "kind": "Ternary",
            "span": node_span(sm, e),
            "width": myw,
            "cond": cond,
            "then": then,
            "else": els,
        }

    if cname == "ConcatenationExpression":
        parts = [_convert_expr(sm, o) for o in e.operands]
        myw = e.type.bitWidth
        ws = [width_of(p) for p in parts]
        if all(w is not None for w in ws) and sum(ws) != myw:
            return unsupported(sm, e, "ConcatenationExpression:width")
        return {
            "kind": "Concat",
            "span": node_span(sm, e),
            "width": myw,
            "parts": parts,
        }

    return unsupported(sm, e)


def ident_target(sm, lhs):
    """Convert an assignment LHS; must come out as an Ident (whole-signal
    assignment). Returns (target_dict, ok)."""
    t = convert_expr(sm, lhs)
    return t, (t is not None and t.get("kind") == "Ident")


# ---------------------------------------------------------------------------
# Statements
# ---------------------------------------------------------------------------

def convert_stmt(sm, s):
    try:
        return _convert_stmt(sm, s)
    except Exception as exc:
        return internal_error(exc)


def _convert_stmt(sm, s):
    if getattr(s, "bad", False):
        return unsupported(sm, s, "InvalidStatement")

    cname = type(s).__name__

    if cname == "BlockStatement":
        if s.blockKind != StatementBlockKind.Sequential:
            return unsupported(
                sm, s, "BlockStatement:" + str(s.blockKind).split(".")[-1]
            )
        body = s.body
        if type(body).__name__ == "StatementList":
            stmts = [convert_stmt(sm, x) for x in body.list]
        else:
            stmts = [convert_stmt(sm, body)]
        return {"kind": "Block", "span": node_span(sm, s), "stmts": stmts}

    if cname == "StatementList":  # bare list (defensive; slang wraps in Block)
        return {
            "kind": "Block",
            "span": node_span(sm, s),
            "stmts": [convert_stmt(sm, x) for x in s.list],
        }

    if cname == "ExpressionStatement":
        e = s.expr
        if type(e).__name__ == "CallExpression":
            return _convert_syscall(sm, s, e)
        if type(e).__name__ != "AssignmentExpression":
            return unsupported(sm, s, "ExpressionStatement:" + type(e).__name__)
        if e.op is not None:  # compound assignment (+=, ...)
            return unsupported(sm, s, "AssignmentExpression:compound")
        if e.timingControl is not None:  # intra-assignment delay/event
            return unsupported(sm, s, "AssignmentExpression:timing")
        target, ok = ident_target(sm, e.left)
        if not ok:
            return unsupported(sm, s, "AssignmentExpression:target")
        value = convert_expr(sm, e.right)
        try:
            if not e.left.type.isFourState:
                value = squash2_wrap(value, e.left.type.bitWidth)
        except Exception:
            pass
        return {
            "kind": "NonblockingAssign" if e.isNonBlocking else "BlockingAssign",
            "span": node_span(sm, s),
            "target": target,
            "value": value,
        }

    if cname == "VariableDeclStatement":
        # Local variable declaration inside a procedural body (self-check
        # tier §f). 2-state locals default-init to 0 (§6.8); 4-state to x.
        sym = s.symbol
        w, two, reason = type_width_2s(sym.type)
        if w is None:
            if reason == "type" and not getattr(sym.type, "isFourState", True):
                reason = "2state"
            return unsupported(sm, s, "VariableDeclStatement:" + reason)
        init = getattr(sym, "initializer", None)
        init_d = convert_expr(sm, init) if init is not None else None
        if two and init_d is not None:
            init_d = squash2_wrap(init_d, w)
        return {
            "kind": "LocalDecl",
            "span": node_span(sm, s),
            "name": sym.name,
            "width": w,
            "two_state": two,
            "init": init_d,
        }

    if cname == "EmptyStatement":
        return {"kind": "Empty", "span": node_span(sm, s)}

    if cname == "ConditionalStatement":
        if s.check != UniquePriorityCheck.None_:
            return unsupported(
                sm, s, "ConditionalStatement:" + str(s.check).split(".")[-1]
            )
        conds = s.conditions
        if len(conds) != 1:
            return unsupported(sm, s, "ConditionalStatement:multi")
        if conds[0].pattern is not None:
            return unsupported(sm, s, "ConditionalStatement:pattern")
        return {
            "kind": "If",
            "span": node_span(sm, s),
            "cond": convert_expr(sm, conds[0].expr),
            "then": convert_stmt(sm, s.ifTrue),
            "else": convert_stmt(sm, s.ifFalse) if s.ifFalse is not None else None,
        }

    if cname == "TimedStatement":  # nested timing control (#10, @(...), ...)
        return unsupported(
            sm, s, "TimedStatement:" + type(s.timing).__name__
        )

    return unsupported(sm, s)


def _convert_syscall(sm, s, e):
    """`$display`/`$write`/`$finish`/`$stop` in statement position ->
    `SysCall` node (self-check tier §f). `$display`/`$write` require the
    first argument to be a string literal (the format); the remaining args
    are M0/self-check expressions with a parallel `arg_signed` list (the
    Lean renderer needs signedness for `%d` widths and refuses to print
    negative signed values — the envelope carries no sign). `$finish`/
    `$stop` arguments (verbosity levels) are ignored. Any other call stays
    `Unsupported` (statement tag `ExpressionStatement:CallExpression`)."""
    try:
        name = e.subroutineName
        is_sys = bool(e.isSystemCall)
    except Exception:
        return unsupported(sm, s, "ExpressionStatement:CallExpression")
    if not is_sys or name not in SYSCALL_FMT + SYSCALL_CTRL:
        return unsupported(sm, s, "ExpressionStatement:CallExpression")
    span = node_span(sm, s)
    if name in SYSCALL_CTRL:
        return {
            "kind": "SysCall",
            "span": span,
            "name": name,
            "format": None,
            "args": [],
            "arg_signed": [],
        }
    try:
        args = list(e.arguments)
    except Exception:
        return unsupported(sm, s, "SysCall:args")
    if not args:  # bare `$display;` prints an empty line
        return {
            "kind": "SysCall",
            "span": span,
            "name": name,
            "format": None,
            "args": [],
            "arg_signed": [],
        }
    first = args[0]
    if type(first).__name__ != "StringLiteral":
        return unsupported(sm, s, "SysCall:format")
    fmt = first.value
    conv = []
    signed = []
    for a in args[1:]:
        conv.append(convert_expr(sm, a))
        try:
            signed.append(bool(a.type.isSigned))
        except Exception:
            signed.append(True)  # unknown signedness: be loud at render time
    return {
        "kind": "SysCall",
        "span": span,
        "name": name,
        "format": fmt,
        "args": conv,
        "arg_signed": signed,
    }


# ---------------------------------------------------------------------------
# Processes
# ---------------------------------------------------------------------------

def convert_procedural_block(sm, m):
    pk = m.procedureKind
    span = sym_span(sm, m)
    if pk == ProceduralBlockKind.Initial:
        # Self-check tier §f: initial blocks are real nodes now (the
        # self-check runner executes them once at time 0). The M0 cycle
        # semantics never sees them — its harness only loads M0 envelopes.
        return {
            "kind": "Initial",
            "span": span,
            "body": convert_stmt(sm, m.body),
        }
    if pk not in (
        ProceduralBlockKind.Always,
        ProceduralBlockKind.AlwaysComb,
        ProceduralBlockKind.AlwaysFF,
    ):
        return unsupported(
            sm, m, "ProceduralBlockSymbol:" + str(pk).split(".")[-1]
        )

    if pk == ProceduralBlockKind.AlwaysComb:
        return {
            "kind": "AlwaysComb",
            "span": span,
            "body": convert_stmt(sm, m.body),
        }

    # always_ff / always: body must be exactly @(posedge <1-bit identifier>)
    style = "always_ff" if pk == ProceduralBlockKind.AlwaysFF else "always"
    body = m.body
    if type(body).__name__ != "TimedStatement":
        return unsupported(sm, m, "ProceduralBlockSymbol:NoEventControl")
    timing = body.timing
    if type(timing).__name__ != "SignalEventControl":
        return unsupported(sm, m, "TimedStatement:" + type(timing).__name__)
    if timing.edge != EdgeKind.PosEdge:
        return unsupported(
            sm, m, "SignalEventControl:" + str(timing.edge).split(".")[-1]
        )
    if timing.iffCondition is not None:
        return unsupported(sm, m, "SignalEventControl:iff")
    clk = convert_expr(sm, timing.expr)
    if clk.get("kind") != "Ident" or clk.get("width") != 1:
        return unsupported(sm, m, "SignalEventControl:clock")
    return {
        "kind": "AlwaysPosedge",
        "span": span,
        "style": style,
        "clock": clk["name"],
        "body": convert_stmt(sm, body.stmt),
    }


def convert_continuous_assign(sm, m):
    if getattr(m, "delay", None) is not None:
        return unsupported(sm, m, "ContinuousAssignSymbol:delay")
    e = m.assignment
    if type(e).__name__ != "AssignmentExpression":
        return unsupported(sm, m, "ContinuousAssignSymbol:" + type(e).__name__)
    if e.op is not None or e.timingControl is not None or e.isNonBlocking:
        return unsupported(sm, m, "ContinuousAssignSymbol:form")
    target, ok = ident_target(sm, e.left)
    if not ok:
        return unsupported(sm, m, "AssignmentExpression:target")
    value = convert_expr(sm, e.right)
    try:
        if not e.left.type.isFourState:
            value = squash2_wrap(value, e.left.type.bitWidth)
    except Exception:
        pass
    return {
        "kind": "Assign",
        "span": node_span(sm, e),
        "target": target,
        "value": value,
    }


# ---------------------------------------------------------------------------
# Declarations and ports
# ---------------------------------------------------------------------------

DIRECTION_MAP = {"In": "in", "Out": "out"}


def convert_port(sm, m):
    d = str(m.direction).split(".")[-1]
    direction = DIRECTION_MAP.get(d)
    if direction is None:  # InOut / Ref
        return unsupported(sm, m, "PortSymbol:" + d)
    w, reason = type_width(m.type)
    if w is None:
        return unsupported(sm, m, "PortSymbol:" + reason)
    return {
        "kind": "Port",
        "span": sym_span(sm, m),
        "name": m.name,
        "dir": direction,
        "width": w,
    }


def convert_var(sm, m):
    w, two, reason = type_width_2s(m.type)
    if w is None:
        if reason == "type" and not getattr(m.type, "isFourState", True):
            reason = "2state"
        return unsupported(sm, m, "VariableSymbol:" + reason)
    init = m.initializer
    init_d = convert_expr(sm, init) if init is not None else None
    if two:
        # 2-state variables start at 0, not x (§6.8) — made explicit so the
        # Var schema stays unchanged; source initializers get the §6.3.1
        # x/z |-> 0 squash.
        if init_d is None:
            init_d = {"kind": "Literal", "span": None, "width": w, "bits": "0" * w}
        else:
            init_d = squash2_wrap(init_d, w)
    return {
        "kind": "Var",
        "span": sym_span(sm, m),
        "name": m.name,
        "width": w,
        "init": init_d,
    }


def convert_net(sm, m):
    nk = str(m.netType.netKind).split(".")[-1]
    if nk != "Wire":
        return unsupported(sm, m, "NetSymbol:" + nk)
    if getattr(m, "delay", None) is not None:
        return unsupported(sm, m, "NetSymbol:delay")
    w, reason = type_width(m.type)
    if w is None:
        return unsupported(sm, m, "NetSymbol:" + reason)
    init = m.initializer
    return {
        "kind": "Net",
        "span": sym_span(sm, m),
        "name": m.name,
        "width": w,
        "init": convert_expr(sm, init) if init is not None else None,
    }


# ---------------------------------------------------------------------------
# Modules / design
# ---------------------------------------------------------------------------

def convert_module(sm, inst):
    body = inst.body
    span = sym_span(sm, body) or sym_span(sm, inst)

    port_names = set()
    for m in body:
        if str(m.kind) == "SymbolKind.Port":
            port_names.add(m.name)

    ports = []
    decls = []
    processes = []
    others = []
    for m in body:
        try:
            k = str(m.kind).split(".")[-1]
            if k == "Port":
                ports.append(convert_port(sm, m))
            elif k in ("Variable", "Net"):
                # Skip the internal symbol backing an ANSI port (same name).
                if m.name in port_names:
                    continue
                if k == "Variable":
                    decls.append(convert_var(sm, m))
                else:
                    decls.append(convert_net(sm, m))
            elif k == "ProceduralBlock":
                processes.append(convert_procedural_block(sm, m))
            elif k == "ContinuousAssign":
                processes.append(convert_continuous_assign(sm, m))
            elif k == "StatementBlock":
                # Scope artifact for statement-level begin/end blocks; its
                # contents appear inside the owning process body.
                continue
            else:
                others.append(unsupported(sm, m, type(m).__name__ + ":" + k))
        except Exception as exc:
            others.append(internal_error(exc))

    return {
        "kind": "Module",
        "span": span,
        "name": inst.name,
        "ports": ports,
        "decls": decls,
        "processes": processes,
        "others": others,
    }


def convert_design(sm, comp):
    modules = []
    others = []
    for inst in comp.getRoot().topInstances:
        try:
            modules.append(convert_module(sm, inst))
        except Exception as exc:
            modules.append(internal_error(exc))
    # $unit-scope members (imports, unit variables, ...) are outside M0.
    try:
        for unit in comp.getCompilationUnits():
            for m in unit:
                others.append(unsupported(sm, m, type(m).__name__))
    except Exception as exc:
        others.append(internal_error(exc))
    return {"kind": "Design", "modules": modules, "others": others}


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def rel_posix(path):
    return os.path.normpath(path).replace(os.sep, "/")


def process_file(source_path):
    global _SOURCE_BYTES
    try:
        with open(source_path, "rb") as f:
            data = f.read()
    except OSError as e:
        raise ExtractError("%s: cannot read: %s" % (source_path, e))
    _SOURCE_BYTES = data

    source_sha256 = hashlib.sha256(data).hexdigest()
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as e:
        raise ExtractError("%s: not valid UTF-8: %s" % (source_path, e))

    tree = SyntaxTree.fromText(text, name=rel_posix(source_path))
    comp = Compilation()
    comp.addSyntaxTree(tree)
    sm = tree.sourceManager

    envelope = {
        "schema_version": SCHEMA_VERSION,
        "language": "systemverilog",
        "frontend": {"name": FRONTEND["name"], "version": FRONTEND["version"]},
        "source_file": rel_posix(source_path),
        "source_sha256": source_sha256,
        "design": convert_design(sm, comp),
        "lean_blocks": [],  # reserved; not scanned in M0
    }

    json_path = source_path + ".json"
    with open(json_path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(envelope, f, indent=2)
        f.write("\n")


def main(argv=None):
    sys.setrecursionlimit(10000)
    parser = argparse.ArgumentParser(
        prog="extract.py",
        description="Extract SystemVerilog sources to sv-0.1 envelope JSON "
        "(run from the repo root; writes <file>.sv.json next to each source).",
    )
    parser.add_argument("sources", nargs="+", metavar="file.sv")
    args = parser.parse_args(argv)

    try:
        for src in args.sources:
            process_file(src)
    except ExtractError as e:
        print("error: %s" % e, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
