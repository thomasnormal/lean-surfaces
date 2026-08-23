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
# THE FRONTEND IS STAMPED BY FAMILY, NEVER BY POINT RELEASE.
#
# This used to be `"version": pyslang.__version__`, i.e. "11.0.0" baked into
# the bytes of all 21 committed envelopes.  Harmless while the round-trip
# gate was simulator-gated and SKIPped; ARMED the moment that gate became an
# unconditional CI step, because the workflow installs pyslang unpinned: the
# next point release would have changed one string in every envelope and
# reported all 21 as DIVERGE on every PR, for a reason unrelated to anyone's
# change.
#
# The family is what the envelope actually depends on -- pyslang 11.x parses
# and elaborates the same way; the patch digit is not a semantic input.  Same
# spelling as `extractors/sv/census.py`, so the two instruments agree.
FRONTEND = {"name": "pyslang",
            "family": "pyslang-%s" % pyslang.__version__.split(".")[0]}

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
# Reduction operators (semantic tier, symbolic mode only): slang enum ->
# the envelope's `Reduce.op` spelling.
REDUCE_OPS = {
    UnaryOperator.BitwiseOr: "|",
    UnaryOperator.BitwiseAnd: "&",
    UnaryOperator.BitwiseXor: "^",
    UnaryOperator.BitwiseNor: "~|",
    UnaryOperator.BitwiseNand: "~&",
    UnaryOperator.BitwiseXnor: "~^",
}
# `case` statement qualifiers (semantic tier): slang enum name -> envelope.
CASE_CHECKS = {
    "None_": "none",
    "Unique": "unique",
    "Unique0": "unique0",
    "Priority": "priority",
}
CASE_CONDITIONS = {
    "Normal": "normal",
    "Inside": "inside",
    # WildcardXOrZ (casex) / WildcardJustZ (casez): NOT in the CV32E40P
    # semantic tier (the core has no casez/casex — see
    # docs/cv32e40p-spec-surface.md "what the RTL corrected"); Unsupported.
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

# Symbolic-mode context (SymCtx) — None in single-file M0/self-check mode.
# Every symbolic-mode behavior change in the shared converters is guarded
# by `_SYM is not None`, keeping single-file output byte-identical.
_SYM = None


def source_text(node):
    """Exact source text of a symbol/statement/expression (via its source
    range's byte offsets), truncated to UNSUPPORTED_TEXT_LIMIT chars.
    Empty string if unavailable."""
    syn = getattr(node, "syntax", None)
    holder = syn if syn is not None else node
    sr = getattr(holder, "sourceRange", None)
    if sr is not None and _SYM is not None:
        # Multi-file compilation: pick the right file's bytes.
        try:
            fname = os.path.normpath(_SYM.sm.getFileName(sr.start))
            data = _SYM.source_map.get(fname)
            if data is not None:
                s, e = sr.start.offset, sr.end.offset
                if 0 <= s <= e <= len(data):
                    txt = data[s:e].decode("utf-8", errors="replace").strip()
                    if txt:
                        return txt[:UNSUPPORTED_TEXT_LIMIT]
        except Exception:
            pass
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


def _multidim_width(t):
    """Total bit width when t is a (possibly multi-dim) packed vector of a
    4-state unsigned scalar with every dimension declared `[N-1:0]`
    (descending, zero-based), else None. The semantic tier treats such a
    vector as one LSB-first bit string; element i of the outermost dim is
    the chunk at offset i*elemW — exactly the `[N-1:0]` layout."""
    try:
        if not t.isFourState or t.isSigned:
            return None
        ct = t.canonicalType
        total = ct.bitWidth
        while type(ct).__name__ == "PackedArrayType":
            rng = ct.range
            n = rng.left - rng.right + 1
            if rng.right != 0 or n <= 0:
                return None
            ct = ct.elementType.canonicalType
        if type(ct).__name__ != "ScalarType":
            return None
        return total
    except Exception:
        return None


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
            if _SYM is not None:
                d = _sym_conversion(sm, e, ow, tw, state_squash)
                if d is not None:
                    return d
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
        if _SYM is not None:
            d = _sym_named_value(sm, e, sym, skind)
            if d is not None:
                return d
        if skind not in ("Variable", "Net"):
            return unsupported(sm, e, "NamedValueExpression:" + skind)
        w, _two, reason = type_width_2s(e.type)
        if w is None and _SYM is not None:
            ew = _sym_enum_width(e.type)
            if ew is not None:
                w = ew
            elif reason == "range":
                # Semantic tier: multi-dim packed vectors are in-vocabulary
                # as ONE bit vector (element selects read/write chunks).
                # Only descending zero-based dims qualify — the select
                # semantics' `chunk i at offset i*elemW` law needs them.
                mw = _multidim_width(e.type)
                if mw is not None:
                    w = mw
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
        if _SYM is not None:
            d = _sym_literal(sm, e, cname)
            if d is not None:
                return d
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
        if sym is None and _SYM is not None:
            # Semantic tier: reduction operators (1-bit result).
            rsym = REDUCE_OPS.get(e.op)
            if rsym is not None:
                return {
                    "kind": "Reduce",
                    "span": node_span(sm, e),
                    "width": 1,
                    "op": rsym,
                    "operand": _convert_expr(sm, e.operand),
                }
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
        if sym is None and _SYM is not None and _SYM.symctx:
            # Symbolic expression positions (parameter defaults, generate
            # bounds, ...) admit the elaboration-arithmetic operators.
            xsym = SYM_BINARY_OPS.get(e.op)
            if xsym is not None:
                return {
                    "kind": "Binary",
                    "span": node_span(sm, e),
                    "width": _safe_width(e),
                    "op": xsym,
                    "left": _convert_expr(sm, e.left),
                    "right": _convert_expr(sm, e.right),
                }
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

    if cname == "CallExpression" and _SYM is not None:
        d = _sym_expr_syscall(sm, e)
        if d is not None:
            return d
        d = _sym_cast_call(sm, e)
        if d is not None:
            return d

    # ---- semantic-tier nodes (symbolic mode only; sv-0.1 unchanged) ----
    if _SYM is not None:
        if cname == "ElementSelectExpression":
            # Bit select / packed element select. The index is a symbolic
            # position (genvar arithmetic like `2**level-1+l` is legal
            # there) — runtime indices parse identically, the extra
            # operators are simply admitted.
            with _SymPos():
                sel = _convert_expr(sm, e.selector)
            return {
                "kind": "BitSel",
                "span": node_span(sm, e),
                "width": _safe_width(e),
                "value": _convert_expr(sm, e.value),
                "index": sel,
            }
        if cname == "RangeSelectExpression":
            skind = str(e.selectionKind).split(".")[-1]
            if skind != "Simple":
                # +: / -: indexed part-selects: no CV32E40P rtl/*.sv file
                # uses them (grep-verified); out of tier, loud.
                return unsupported(sm, e, "RangeSelectExpression:" + skind)
            with _SymPos():
                msb = _convert_expr(sm, e.left)
                lsb = _convert_expr(sm, e.right)
            return {
                "kind": "PartSel",
                "span": node_span(sm, e),
                "width": _safe_width(e),
                "value": _convert_expr(sm, e.value),
                "msb": msb,
                "lsb": lsb,
            }
        if cname == "ReplicationExpression":
            with _SymPos():
                cnt = _convert_expr(sm, e.count)
            return {
                "kind": "Repl",
                "span": node_span(sm, e),
                "width": _safe_width(e),
                "count": cnt,
                "operand": _convert_expr(sm, e.concat),
            }

    return unsupported(sm, e)


def _sym_cast_call(sm, e):
    """$signed/$unsigned in expression position (semantic tier): a Cast
    node. Width-preserving (slang gives the call the operand's width), so
    the cast itself changes no bits — signedness matters only through the
    consuming operator (order comparisons are emitted `s<`-style when both
    operands are signed, §11.8.1). Returns None for any other call."""
    try:
        name = e.subroutineName
        if not e.isSystemCall or name not in ("$signed", "$unsigned"):
            return None
        args = list(e.arguments)
    except Exception:
        return None
    if len(args) != 1:
        return unsupported(sm, e, "CallExpression:arity")
    operand = _convert_expr(sm, args[0])
    ow = width_of(operand)
    myw = _safe_width(e)
    if ow is not None and myw is not None and ow != myw:
        return unsupported(sm, e, "CallExpression:cast-width")
    return {
        "kind": "Cast",
        "span": node_span(sm, e),
        "width": myw,
        "signed": name == "$signed",
        "operand": operand,
    }


def ident_target(sm, lhs):
    """Convert an assignment LHS; must come out as an Ident (whole-signal
    assignment). Returns (target_dict, ok)."""
    t = convert_expr(sm, lhs)
    return t, (t is not None and t.get("kind") == "Ident")


def _target_shape_ok(t):
    """Semantic-tier LHS shapes: Ident, or a single BitSel/PartSel whose
    base is an Ident (no nested selects, no concat LHS — the CV32E40P
    provable files use none of those on the left)."""
    if t is None:
        return False
    k = t.get("kind")
    if k == "Ident":
        return True
    if k in ("BitSel", "PartSel"):
        base = t.get("value")
        return base is not None and base.get("kind") == "Ident"
    return False


def select_target(sm, lhs):
    """Assignment LHS in symbolic mode: Ident / BitSel / PartSel over an
    Ident. Falls back to the M0 Ident-only rule in single-file mode."""
    if _SYM is None:
        return ident_target(sm, lhs)
    t = convert_expr(sm, lhs)
    return t, _target_shape_ok(t)


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
        target, ok = select_target(sm, e.left)
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

    if cname == "CaseStatement" and _SYM is not None:
        check = CASE_CHECKS.get(str(s.check).split(".")[-1])
        cond = CASE_CONDITIONS.get(str(s.condition).split(".")[-1])
        if check is None:
            return unsupported(sm, s, "CaseStatement:"
                               + str(s.check).split(".")[-1])
        if cond is None:
            # casez/casex: not in the CV32E40P tier (the core uses
            # `case … inside`, §12.5.4 — never casez).
            return unsupported(sm, s, "CaseStatement:"
                               + str(s.condition).split(".")[-1])
        items = []
        for it in s.items:
            with _SymPos():
                pats = [_convert_expr(sm, ex) for ex in it.expressions]
            items.append({
                "kind": "CaseItem",
                "patterns": pats,
                "body": convert_stmt(sm, it.stmt),
            })
        return {
            "kind": "Case",
            "span": node_span(sm, s),
            "check": check,
            "match": cond,
            "subject": convert_expr(sm, s.expr),
            "items": items,
            "default": convert_stmt(sm, s.defaultCase)
            if s.defaultCase is not None else None,
        }

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
    # — or, in symbolic mode, @(posedge clk or negedge rst_n) (the async
    # active-low reset event list every clocked CV32E40P module uses).
    style = "always_ff" if pk == ProceduralBlockKind.AlwaysFF else "always"
    body = m.body
    if type(body).__name__ != "TimedStatement":
        return unsupported(sm, m, "ProceduralBlockSymbol:NoEventControl")
    timing = body.timing
    if type(timing).__name__ == "EventListControl" and _SYM is not None:
        d = _sym_areset_process(sm, m, body, timing, style)
        if d is not None:
            return d
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


def _sym_areset_process(sm, m, body, timing, style):
    """`@(posedge clk or negedge rst_n)` (or the comma form) with 1-bit
    identifier events -> AlwaysPosedge node with an extra `areset_n` field
    (semantic tier T-reset). Any other event list: None (falls through to
    the M0 Unsupported path)."""
    try:
        events = list(timing.events)
    except Exception:
        return None
    if len(events) != 2:
        return None
    clk_name = None
    rst_name = None
    for ev in events:
        if type(ev).__name__ != "SignalEventControl":
            return None
        if getattr(ev, "iffCondition", None) is not None:
            return None
        sig = convert_expr(sm, ev.expr)
        if sig.get("kind") != "Ident" or sig.get("width") != 1:
            return None
        if ev.edge == EdgeKind.PosEdge and clk_name is None:
            clk_name = sig["name"]
        elif ev.edge == EdgeKind.NegEdge and rst_name is None:
            rst_name = sig["name"]
        else:
            return None
    if clk_name is None or rst_name is None:
        return None
    return {
        "kind": "AlwaysPosedge",
        "span": sym_span(sm, m),
        "style": style,
        "clock": clk_name,
        "areset_n": rst_name,
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
    target, ok = select_target(sm, e.left)
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
# Symbolic mode (schema sv-0.2, `--top`): multi-file compilation for name
# resolution; parameters/generate/enums stay SYMBOLIC (never folded, never
# unrolled). See docs/sv-envelope-schema.md "Symbolic mode".
#
# Symbolic-recovery method (and its limits):
#   1. Wherever slang retains a *bound* expression, we convert the bound
#      AST: parameter defaults (`ParameterSymbol.initializer`), generate-for
#      headers (`GenerateBlockArraySymbol.initialExpression/stopExpression/
#      iterExpression`), generate-if conditions
#      (`GenerateBlockSymbol.conditionExpression`), and every RHS. In these
#      trees a parameter reference is still a NamedValueExpression pointing
#      at the ParameterSymbol — emitted as ParamRef, never its value.
#   2. The one place slang folds without keeping a bound expression is the
#      packed DIMENSIONS of declared types (DeclaredType resolves them to
#      integer ConstantRange). Those are recovered from the declaration's
#      *syntax tree* (`declaredType.typeSyntax` -> VariableDimension ->
#      SimpleRangeSelect) with a SyntaxKind-driven converter; identifiers
#      are classified by `Scope.lookupName` on the top module's body scope.
#   3. `resolved` fields carry the defaults-elaborated integers alongside
#      every symbolic form (phase-2 cross-checks; secondary by contract).
# Known limits (documented in the schema): syntax-recovered expressions are
# not re-type-checked (no width fields); dimension identifiers must be
# visible from the top module's scope (true for wildcard-imported package
# params; a package-private name would fall back to Unsupported + resolved);
# genvar references are recognized by name against the enclosing generate
# stack; expression-node `width` fields inside processes are elaborated
# under DEFAULT parameter values (cross-check only — the binding widths are
# the symbolic ones on declarations).
# ---------------------------------------------------------------------------

from pyslang.syntax import SyntaxKind

SYM_SYSCALLS = ("$clog2", "$bits", "$high", "$size")

# Extra operators admitted in symbolic expression positions only
# (parameter defaults, localparam exprs, generate headers/conds, dims).
SYM_BINARY_OPS = {
    BinaryOperator.Multiply: "*",
    BinaryOperator.Divide: "/",
    BinaryOperator.Mod: "%",
    BinaryOperator.Power: "**",
    BinaryOperator.LogicalShiftLeft: "<<",
    BinaryOperator.LogicalShiftRight: ">>",
    BinaryOperator.ArithmeticShiftLeft: "<<<",
    BinaryOperator.ArithmeticShiftRight: ">>>",
}

SYM_SYNTAX_BINOPS = {
    SyntaxKind.AddExpression: "+",
    SyntaxKind.SubtractExpression: "-",
    SyntaxKind.MultiplyExpression: "*",
    SyntaxKind.DivideExpression: "/",
    SyntaxKind.ModExpression: "%",
    SyntaxKind.PowerExpression: "**",
    SyntaxKind.LogicalShiftLeftExpression: "<<",
    SyntaxKind.LogicalShiftRightExpression: ">>",
    SyntaxKind.ArithmeticShiftLeftExpression: "<<<",
    SyntaxKind.ArithmeticShiftRightExpression: ">>>",
    SyntaxKind.LessThanExpression: "<",
    SyntaxKind.LessThanEqualExpression: "<=",
    SyntaxKind.GreaterThanExpression: ">",
    SyntaxKind.GreaterThanEqualExpression: ">=",
    SyntaxKind.EqualityExpression: "==",
    SyntaxKind.InequalityExpression: "!=",
    SyntaxKind.BinaryAndExpression: "&",
    SyntaxKind.BinaryOrExpression: "|",
    SyntaxKind.BinaryXorExpression: "^",
    SyntaxKind.LogicalAndExpression: "&&",
    SyntaxKind.LogicalOrExpression: "||",
}

SYM_SYNTAX_UNOPS = {
    SyntaxKind.UnaryMinusExpression: "-",
    SyntaxKind.UnaryPlusExpression: "+",
    SyntaxKind.UnaryBitwiseNotExpression: "~",
    SyntaxKind.UnaryLogicalNotExpression: "!",
}


class SymCtx:
    """State of one symbolic extraction (set as the module global _SYM)."""

    def __init__(self, comp, sm, source_map):
        self.comp = comp
        self.sm = sm
        self.source_map = source_map  # normpath -> bytes
        self.scope = None             # top module body scope (lookupName)
        self.genvars = []             # stack of enclosing genvar names
        self.symctx = False           # inside a symbolic expression position
        self.enum_nodes = []          # EnumType nodes, registration order
        self.enum_by_key = {}         # (name, from_package) -> node
        self.packages = set()         # package names actually referenced


class _SymPos:
    """with _SymPos(): mark a symbolic expression position."""

    def __enter__(self):
        self.saved = _SYM.symctx
        _SYM.symctx = True

    def __exit__(self, *exc):
        _SYM.symctx = self.saved
        return False


def _safe_width(e):
    try:
        return e.type.bitWidth
    except Exception:
        return None


def _cv_int(cv):
    """ConstantValue -> int, MSB-first bits string (x/z), or None."""
    try:
        sv = cv.value
        if type(sv).__name__ != "SVInt":
            return None
        try:
            return int(sv)
        except Exception:
            return svint_bits(sv)
    except Exception:
        return None


def _pkg_of(sym):
    """Package name a symbol lives in (via 'pkg::name' hierarchicalPath),
    else None. Records the package in the context."""
    try:
        hp = sym.hierarchicalPath
        if "::" in hp:
            pkg = hp.split("::", 1)[0]
            _SYM.packages.add(pkg)
            return pkg
    except Exception:
        pass
    return None


def _sym_enum_width(t):
    """Resolved width when t is (an alias of) a 4-state enum, else None."""
    try:
        ct = t.canonicalType
        if type(ct).__name__ == "EnumType" and ct.isFourState:
            return ct.bitWidth
    except Exception:
        pass
    return None


def _enum_name_of(t):
    """(name, from_package) for an enum type: the typedef alias name when
    there is one; anonymous enums get slang's deterministic 'e$N' name."""
    from_package = None
    if type(t).__name__ == "TypeAliasType":
        name = t.name
        syn = getattr(t, "syntax", None)
        # Provenance: a typedef inside a package prints pkg-scoped members.
        ct = t.canonicalType
        for ev in _enum_members(ct):
            from_package = _pkg_of(ev)
            break
        return name, from_package
    # Anonymous: str(t) ends with '<owner>.e$N' after the closing brace.
    try:
        tail = str(t).rsplit("}", 1)[1]
        name = tail.rsplit(".", 1)[-1] or "$anon_enum"
    except Exception:
        name = "$anon_enum"
    for ev in _enum_members(t.canonicalType):
        from_package = _pkg_of(ev)
        break
    return name, from_package


def _enum_members(ct):
    try:
        return [m for m in ct if type(m).__name__ == "EnumValueSymbol"]
    except Exception:
        return []


def _enum_base_node(sm, ct):
    """PackedType node for the enum's base type: symbolic packed dims
    recovered from the EnumType syntax when possible, resolved width from
    elaboration."""
    resolved = None
    try:
        resolved = ct.bitWidth
    except Exception:
        pass
    packed = None
    try:
        syn = ct.syntax
        if syn is not None and syn.kind == SyntaxKind.EnumType:
            for c in syn:
                k = getattr(c, "kind", None)
                if k in (SyntaxKind.LogicType, SyntaxKind.RegType,
                         SyntaxKind.BitType):
                    packed = _syntax_packed_dims(sm, c)
                    break
    except Exception:
        packed = None
    return {"kind": "PackedType", "packed": packed, "resolved": resolved}


def register_enum(sm, t):
    """Ensure the enum type behind t is in the module's `types` list;
    returns (name, from_package)."""
    name, from_package = _enum_name_of(t)
    key = (name, from_package)
    if key in _SYM.enum_by_key:
        return key
    ct = t.canonicalType
    node = {
        "kind": "EnumType",
        "span": range_span(sm, getattr(ct.syntax, "sourceRange", None))
        if getattr(ct, "syntax", None) is not None else None,
        "name": name,
        "from_package": from_package,
        "base_width": _enum_base_node(sm, ct),
        "members": [
            {"name": ev.name, "value": _cv_int(ev.value)}
            for ev in _enum_members(ct)
        ],
    }
    _SYM.enum_by_key[key] = node
    _SYM.enum_nodes.append(node)
    return key


def _sym_named_value(sm, e, sym, skind):
    """Symbolic-mode NamedValueExpression handling: ParamRef / GenvarRef /
    EnumRef. Returns None to fall through to the M0 Ident path."""
    name = sym.name
    if name in _SYM.genvars:
        # Loop variable of an enclosing generate-for: both the module-level
        # genvar symbol (headers) and the per-block local parameter slang
        # materializes (bodies) resolve here, by name.
        return {"kind": "GenvarRef", "span": node_span(sm, e), "name": name}
    if skind == "Parameter":
        d = {"kind": "ParamRef", "span": node_span(sm, e), "name": name}
        pkg = _pkg_of(sym)
        if pkg is not None:
            d["from_package"] = pkg
        return d
    if skind == "EnumValue":
        tname, pkg = register_enum(sm, sym.type)
        return {
            "kind": "EnumRef",
            "span": node_span(sm, e),
            "type": tname,
            "member": name,
            "from_package": pkg,
        }
    if skind == "Genvar":
        return {"kind": "GenvarRef", "span": node_span(sm, e), "name": name}
    return None


def _sym_literal(sm, e, cname):
    """Symbolic-mode literals: '0/'1/'x/'z -> Fill (their width is
    context-propagated, i.e. potentially a parameter value); unsized
    decimal literals -> Int. Sized literals fall through to M0 Literal."""
    if cname == "UnbasedUnsizedIntegerLiteral":
        sv = e.value
        bits = svint_bits(sv)
        return {
            "kind": "Fill",
            "span": node_span(sm, e),
            "bit": bits[0] if bits else "0",
            "resolved_width": sv.bitWidth,
        }
    try:
        if e.syntax is not None and \
                e.syntax.kind == SyntaxKind.IntegerLiteralExpression:
            sv = e.value
            return {
                "kind": "Int",
                "span": node_span(sm, e),
                "value": int(sv),
                "resolved_width": sv.bitWidth,
            }
    except Exception:
        pass
    return None


def _has_sym_refs(d):
    """True if a converted tree contains symbolic reference nodes whose
    value must not be constant-folded."""
    if isinstance(d, dict):
        if d.get("kind") in ("ParamRef", "GenvarRef", "EnumRef", "SysCall",
                             "Fill"):
            return True
        return any(_has_sym_refs(v) for v in d.values())
    if isinstance(d, list):
        return any(_has_sym_refs(v) for v in d)
    return False


def _sym_conversion(sm, e, ow, tw, state_squash):
    """Symbolic-mode width-changing implicit conversion. Returns None to
    fall through to the M0 fold/Resize path (safe when the operand holds
    no symbolic references)."""
    op = e.operand
    ocname = type(op).__name__
    if ocname == "UnbasedUnsizedIntegerLiteral":
        sv = op.value
        bits = svint_bits(sv)
        return {
            "kind": "Fill",
            "span": node_span(sm, e),
            "bit": bits[0] if bits else "0",
            "resolved_width": tw,
        }
    if ocname == "IntegerLiteral":
        try:
            if op.syntax is not None and \
                    op.syntax.kind == SyntaxKind.IntegerLiteralExpression:
                return {
                    "kind": "Int",
                    "span": node_span(sm, e),
                    "value": int(op.value),
                    "resolved_width": tw,
                }
        except Exception:
            pass
        return None
    inner = _convert_expr(sm, op)
    try:
        resizable = (
            op.type.isIntegral and e.type.isIntegral and not op.type.isSigned
        )
    except Exception:
        resizable = False
    if not resizable and not _has_sym_refs(inner):
        # Signed/exotic constant operand without symbolic refs: slang's
        # fold (M0 path) is the only representation we have. NOTE the
        # recorded limitation: the folded width is defaults-elaborated.
        return None
    if not resizable:
        return unsupported(sm, e, "ConversionExpression:width")
    # Unsigned operands ALWAYS emit Resize in symbolic mode — the target
    # width is context-propagated (parameter-dependent), so a folded
    # literal would bake in the defaults-elaborated width and be silently
    # wrong at other family points. `Resize.width` stays metadata; the
    # Lean side resizes to the *instantiated* context width.
    if state_squash:
        inner = {"kind": "Squash2", "span": node_span(sm, e), "width": ow,
                 "operand": inner}
    return {
        "kind": "Resize",
        "span": node_span(sm, e),
        "width": tw,
        "operand": inner,
    }


def _sym_expr_syscall(sm, e):
    """$clog2/$bits/$high/$size in expression position -> SysCall node
    {kind, span, name, args, resolved}. Returns None for any other call."""
    try:
        name = e.subroutineName
        if not e.isSystemCall or name not in SYM_SYSCALLS:
            return None
        args = [_convert_expr(sm, a) for a in e.arguments]
    except Exception:
        return None
    resolved = None
    try:
        c = e.constant
        if c is not None:
            resolved = _cv_int(c)
    except Exception:
        pass
    return {
        "kind": "SysCall",
        "span": node_span(sm, e),
        "name": name,
        "args": args,
        "resolved": resolved,
    }


def convert_sym_expr(sm, e):
    """Bound expression in a symbolic position (defaults, generate headers,
    conditions): full symbolic vocabulary enabled."""
    with _SymPos():
        return convert_expr(sm, e)


# --- syntactic recovery of packed dimensions -------------------------------

def _syntax_children(sn):
    out = []
    try:
        for c in sn:
            if hasattr(c, "kind") and type(c.kind).__name__ == "SyntaxKind":
                out.append(c)
    except TypeError:
        pass
    return out


def _syntax_span(sm, sn):
    return range_span(sm, getattr(sn, "sourceRange", None))


def _syntax_unsupported(sm, sn, tag=None):
    txt = ""
    try:
        txt = str(sn).strip()[:UNSUPPORTED_TEXT_LIMIT]
    except Exception:
        pass
    return {
        "kind": "Unsupported",
        "span": _syntax_span(sm, sn),
        "sv_kind": tag if tag is not None
        else "Syntax:" + str(getattr(sn, "kind", "?")).split(".")[-1],
        "text": txt,
    }


def _syntax_expr(sm, sn):
    """Syntax expression -> symbolic node. Used only where slang keeps no
    bound expression (declared-type dimensions). Identifiers are resolved
    with lookupName on the top module's body scope."""
    try:
        return _syntax_expr_inner(sm, sn)
    except Exception as exc:
        return internal_error(exc)


def _syntax_expr_inner(sm, sn):
    k = sn.kind
    if k == SyntaxKind.ParenthesizedExpression:
        kids = _syntax_children(sn)
        return _syntax_expr(sm, kids[0]) if len(kids) == 1 \
            else _syntax_unsupported(sm, sn)
    if k == SyntaxKind.IntegerLiteralExpression:
        try:
            return {
                "kind": "Int",
                "span": _syntax_span(sm, sn),
                "value": int(str(sn).strip().replace("_", "")),
                "resolved_width": None,
            }
        except ValueError:
            return _syntax_unsupported(sm, sn)
    if k == SyntaxKind.IdentifierName:
        name = str(sn).strip()
        return _syntax_name(sm, sn, _SYM.scope, name, None)
    if k == SyntaxKind.ScopedName:
        kids = _syntax_children(sn)
        if len(kids) == 2 and kids[0].kind == SyntaxKind.IdentifierName:
            pkg_name = str(kids[0]).strip()
            pkg = None
            try:
                pkg = _SYM.comp.getPackage(pkg_name)
            except Exception:
                pkg = None
            if pkg is not None and kids[1].kind == SyntaxKind.IdentifierName:
                return _syntax_name(sm, sn, pkg, str(kids[1]).strip(),
                                    pkg_name)
        return _syntax_unsupported(sm, sn)
    if k in SYM_SYNTAX_BINOPS:
        kids = _syntax_children(sn)
        if len(kids) != 2:
            return _syntax_unsupported(sm, sn)
        return {
            "kind": "Binary",
            "span": _syntax_span(sm, sn),
            "width": None,
            "op": SYM_SYNTAX_BINOPS[k],
            "left": _syntax_expr(sm, kids[0]),
            "right": _syntax_expr(sm, kids[1]),
        }
    if k in SYM_SYNTAX_UNOPS:
        kids = _syntax_children(sn)
        if len(kids) != 1:
            return _syntax_unsupported(sm, sn)
        return {
            "kind": "Unary",
            "span": _syntax_span(sm, sn),
            "width": None,
            "op": SYM_SYNTAX_UNOPS[k],
            "operand": _syntax_expr(sm, kids[0]),
        }
    if k == SyntaxKind.ConditionalExpression:
        kids = _syntax_children(sn)
        if len(kids) == 3:
            cond = kids[0]
            if cond.kind == SyntaxKind.ConditionalPredicate:
                inner = _syntax_children(cond)
                if len(inner) != 1:
                    return _syntax_unsupported(sm, sn)
                cond = inner[0]
                if type(cond).__name__ == "ConditionalPatternSyntax" or \
                        cond.kind == SyntaxKind.ConditionalPattern:
                    sub = _syntax_children(cond)
                    if len(sub) != 1:
                        return _syntax_unsupported(sm, sn)
                    cond = sub[0]
            return {
                "kind": "Ternary",
                "span": _syntax_span(sm, sn),
                "width": None,
                "cond": _syntax_expr(sm, cond),
                "then": _syntax_expr(sm, kids[1]),
                "else": _syntax_expr(sm, kids[2]),
            }
        return _syntax_unsupported(sm, sn)
    if k == SyntaxKind.InvocationExpression:
        kids = _syntax_children(sn)
        if len(kids) == 2 and kids[0].kind == SyntaxKind.SystemName:
            name = str(kids[0]).strip()
            if name in SYM_SYSCALLS:
                args = []
                for a in _syntax_children(kids[1]):
                    if a.kind == SyntaxKind.OrderedArgument:
                        sub = _syntax_children(a)
                        # slang wraps call arguments in property-expr
                        # nodes (assertion-capable call sites): unwrap.
                        while len(sub) == 1 and sub[0].kind in (
                                SyntaxKind.SimplePropertyExpr,
                                SyntaxKind.SimpleSequenceExpr):
                            sub = _syntax_children(sub[0])
                        if len(sub) == 1:
                            args.append(_syntax_expr(sm, sub[0]))
                        else:
                            args.append(_syntax_unsupported(sm, a))
                    else:
                        args.append(_syntax_unsupported(sm, a))
                return {
                    "kind": "SysCall",
                    "span": _syntax_span(sm, sn),
                    "name": name,
                    "args": args,
                    "resolved": None,
                }
        return _syntax_unsupported(sm, sn)
    return _syntax_unsupported(sm, sn)


def _syntax_name(sm, sn, scope, name, from_package):
    sym = None
    try:
        sym = scope.lookupName(name)
    except Exception:
        sym = None
    if sym is None:
        return _syntax_unsupported(sm, sn, "Syntax:Identifier:unresolved")
    cls = type(sym).__name__
    if cls == "ParameterSymbol":
        d = {"kind": "ParamRef", "span": _syntax_span(sm, sn), "name": name}
        pkg = from_package if from_package is not None else _pkg_of(sym)
        if pkg is not None:
            d["from_package"] = pkg
            _SYM.packages.add(pkg)
        return d
    if cls == "GenvarSymbol" or name in _SYM.genvars:
        return {"kind": "GenvarRef", "span": _syntax_span(sm, sn),
                "name": name}
    if cls == "EnumValueSymbol":
        tname, pkg = register_enum(sm, sym.type)
        return {
            "kind": "EnumRef",
            "span": _syntax_span(sm, sn),
            "type": tname,
            "member": name,
            "from_package": pkg,
        }
    return _syntax_unsupported(sm, sn, "Syntax:Identifier:" + cls)


def _syntax_packed_dims(sm, type_syntax):
    """[{msb, lsb}, ...] recovered from a LogicType/RegType/BitType syntax
    node's VariableDimension children, or None when any is irregular."""
    dims = []
    for c in _syntax_children(type_syntax):
        if c.kind != SyntaxKind.VariableDimension:
            continue
        spec = None
        for s in _syntax_children(c):
            if s.kind == SyntaxKind.RangeDimensionSpecifier:
                spec = s
                break
        if spec is None:
            return None
        sel = _syntax_children(spec)
        if len(sel) != 1 or sel[0].kind != SyntaxKind.SimpleRangeSelect:
            return None
        lr = _syntax_children(sel[0])
        if len(lr) != 2:
            return None
        with _SymPos():
            dims.append({
                "msb": _syntax_expr(sm, lr[0]),
                "lsb": _syntax_expr(sm, lr[1]),
            })
    return dims if dims else None


# --- symbolic declarations -------------------------------------------------

def _dtype_sym(sm, t, type_syntax):
    """(dtype-node, None) or (None, reason-tag) for a declared type in
    symbolic mode: TypeRef for enums, PackedType (symbolic dims primary,
    resolved secondary) for unsigned 4-state scalars/packed vectors."""
    try:
        ct = t.canonicalType
        if type(ct).__name__ == "EnumType":
            if not ct.isFourState:
                return None, "2state"
            name, pkg = register_enum(sm, t)
            return {
                "kind": "TypeRef",
                "name": name,
                "from_package": pkg,
                "resolved": ct.bitWidth,
            }, None
        if not t.isFourState:
            return None, "2state"
        if t.isSigned:
            return None, "signed"
        cname = type(ct).__name__
        if cname == "ScalarType":
            return {"kind": "PackedType", "packed": [], "resolved": 1}, None
        if cname == "PackedArrayType":
            ndims = 0
            cur = ct
            while type(cur).__name__ == "PackedArrayType":
                ndims += 1
                cur = cur.elementType.canonicalType
            if type(cur).__name__ != "ScalarType":
                return None, "type"
            packed = None
            if type_syntax is not None and type_syntax.kind in (
                    SyntaxKind.LogicType, SyntaxKind.RegType):
                packed = _syntax_packed_dims(sm, type_syntax)
                if packed is not None and len(packed) != ndims:
                    packed = None
            return {
                "kind": "PackedType",
                "packed": packed,
                "resolved": ct.bitWidth,
            }, None
        return None, "type"
    except Exception:
        return None, "type"


def _decl_type_syntax(sym):
    try:
        return sym.declaredType.typeSyntax
    except Exception:
        return None


def convert_port_sym(sm, m):
    d = str(m.direction).split(".")[-1]
    direction = DIRECTION_MAP.get(d)
    if direction is None:
        return unsupported(sm, m, "PortSymbol:" + d)
    isym = getattr(m, "internalSymbol", None)
    tsyn = _decl_type_syntax(isym) if isym is not None else None
    dtype, reason = _dtype_sym(sm, m.type, tsyn)
    if dtype is None:
        return unsupported(sm, m, "PortSymbol:" + reason)
    return {
        "kind": "Port",
        "span": sym_span(sm, m),
        "name": m.name,
        "dir": direction,
        "width": dtype,
    }


def convert_var_sym(sm, m):
    dtype, reason = _dtype_sym(sm, m.type, _decl_type_syntax(m))
    if dtype is None:
        return unsupported(sm, m, "VariableSymbol:" + reason)
    init = m.initializer
    return {
        "kind": "Var",
        "span": sym_span(sm, m),
        "name": m.name,
        "width": dtype,
        "init": convert_expr(sm, init) if init is not None else None,
    }


def convert_net_sym(sm, m):
    nk = str(m.netType.netKind).split(".")[-1]
    if nk != "Wire":
        return unsupported(sm, m, "NetSymbol:" + nk)
    if getattr(m, "delay", None) is not None:
        return unsupported(sm, m, "NetSymbol:delay")
    dtype, reason = _dtype_sym(sm, m.type, _decl_type_syntax(m))
    if dtype is None:
        return unsupported(sm, m, "NetSymbol:" + reason)
    init = m.initializer
    return {
        "kind": "Net",
        "span": sym_span(sm, m),
        "name": m.name,
        "width": dtype,
        "init": convert_expr(sm, init) if init is not None else None,
    }


def _param_width_type(sm, m):
    """Width-only fallback type for a DECLARED (non-implicit) parameter
    type that `_dtype_sym` cannot represent (2-state and/or signed keyword
    types: `bit`, `int`, `int unsigned`, `integer`, ...). A parameter's
    VALUE is a compile-time integer, so 4-state-ness cannot matter for the
    value tier — but its declared WIDTH governs every expression containing
    the ParamRef (`parameter bit FALL_THROUGH` makes `FALL_THROUGH &
    push_i` a 1-bit `&`; dropping the type to `null` made the Lean side
    assume 32 bits and x-poison cv32e40p_fifo's `empty_o` — the envelope
    bug this fixes, found by the phase-2 differential harness). Concrete
    bounds are emitted only when the type syntax carries NO dimensions
    (keyword-typed: width fixed at every family point); a dimensioned
    unrepresentable type emits `packed: null` (unrecoverable) so the Lean
    side is LOUD where it would otherwise be silently wrong."""
    try:
        t = m.type
        if not t.isIntegral:
            return None
        w = int(t.bitWidth)
        dims = getattr(_decl_type_syntax(m), "dimensions", None)
        ndims = sum(1 for _ in dims) if dims is not None else 0
    except Exception:
        return None
    if ndims != 0:
        return {"kind": "PackedType", "packed": None, "resolved": w}
    if w == 1:
        return {"kind": "PackedType", "packed": [], "resolved": 1}
    span = sym_span(sm, m)
    return {
        "kind": "PackedType",
        "packed": [{
            "msb": {"kind": "Int", "span": span, "value": w - 1,
                    "resolved_width": 32},
            "lsb": {"kind": "Int", "span": span, "value": 0,
                    "resolved_width": 32},
        }],
        "resolved": w,
    }


def convert_param_sym(sm, m):
    """ParameterSymbol -> ParameterDecl (module parameter) or LocalParam
    (localparam). `default`/`expr` is the SYMBOLIC bound initializer;
    `resolved` the defaults-elaborated value (secondary). `type` is the
    declared type when representable, a width-only `PackedType` for
    declared-but-2-state/signed keyword types (`_param_width_type` — the
    width is semantics, never dropped), and `null` ONLY for a genuinely
    implicit type."""
    tsyn = _decl_type_syntax(m)
    ptype = None
    if tsyn is not None and tsyn.kind != SyntaxKind.ImplicitType:
        ptype, _reason = _dtype_sym(sm, m.type, tsyn)
        if ptype is None:
            ptype = _param_width_type(sm, m)
    init = getattr(m, "initializer", None)
    init_d = convert_sym_expr(sm, init) if init is not None else None
    resolved = None
    try:
        resolved = _cv_int(m.value)
    except Exception:
        pass
    if m.isLocalParam:
        return {
            "kind": "LocalParam",
            "span": sym_span(sm, m),
            "name": m.name,
            "type": ptype,
            "expr": init_d,
            "resolved": resolved,
        }
    return {
        "kind": "ParameterDecl",
        "span": sym_span(sm, m),
        "name": m.name,
        "type": ptype,
        "default": init_d,
        "resolved": resolved,
    }


# --- generate constructs ---------------------------------------------------

def _genstep(sm, e):
    """Generate-for iteration expression; `i++`/`i--` become Unary nodes."""
    if type(e).__name__ == "UnaryExpression":
        opname = str(e.op).split(".")[-1]
        if opname in ("Preincrement", "Postincrement"):
            op = "++"
        elif opname in ("Predecrement", "Postdecrement"):
            op = "--"
        else:
            op = None
        if op is not None:
            return {
                "kind": "Unary",
                "span": node_span(sm, e),
                "width": None,
                "op": op,
                "operand": convert_sym_expr(sm, e.operand),
            }
    return convert_sym_expr(sm, e)


def convert_generate_for(sm, m):
    """GenerateBlockArraySymbol -> ONE GenerateFor node: genvar + symbolic
    header expressions + body template (never unrolled). The template is
    entries[0]'s members — every entry is bound from the same syntax; the
    genvar surfaces as GenvarRef wherever it is referenced."""
    genvar = None
    try:
        genvar = m.loopVariable.name
    except Exception:
        pass
    span = sym_span(sm, m)
    if not genvar:
        return unsupported(sm, m, "GenerateBlockArraySymbol:noloopvar")
    _SYM.genvars.append(genvar)
    try:
        init = convert_sym_expr(sm, m.initialExpression)
        bound = convert_sym_expr(sm, m.stopExpression)
        step = _genstep(sm, m.iterExpression)
        entries = []
        try:
            entries = list(m.entries)
        except Exception:
            pass
        if entries:
            body = convert_members_sym(sm, entries[0])
        else:
            # Zero instances under default parameters: no bound template
            # exists; the body is kept as raw source (honest limit).
            body = [_syntax_unsupported(sm, m.syntax,
                                        "GenerateFor:no-template")]
        return {
            "kind": "GenerateFor",
            "span": span,
            "label": m.name if m.name else None,
            "genvar": genvar,
            "init": init,
            "bound": bound,
            "step": step,
            "resolved_count": len(entries),
            "body": body,
        }
    finally:
        _SYM.genvars.pop()


def _ifgen_of(block_syntax):
    """The IfGenerate syntax owning a generate block, plus whether the
    block is the else branch. (None, False) when not an if-generate."""
    p = getattr(block_syntax, "parent", None)
    if p is None:
        return None, False
    if p.kind == SyntaxKind.IfGenerate:
        return p, False
    if p.kind == SyntaxKind.ElseClause:
        pp = getattr(p, "parent", None)
        if pp is not None and pp.kind == SyntaxKind.IfGenerate:
            return pp, True
    return None, False


def _ifgen_key(syn):
    try:
        return syn.sourceRange.start.offset
    except Exception:
        return id(syn)


def convert_generate_ifs(sm, members):
    """A run of GenerateBlockSymbols originating from one if-generate
    (including else-if chains) -> ONE nested GenerateIf node. `members` is
    the full consecutive run; branches pair up via their IfGenerate syntax."""
    recs = {}
    order = []
    for m in members:
        ifgen, is_else = _ifgen_of(m.syntax)
        key = _ifgen_key(ifgen)
        if key not in recs:
            recs[key] = {"syntax": ifgen, "then": None, "else": None}
            order.append(key)
        recs[key]["else" if is_else else "then"] = m
    # An if-generate nested in another's else clause forms an else-if chain.
    chained = set()
    for key in order:
        syn = recs[key]["syntax"]
        p = getattr(syn, "parent", None)
        if p is not None and p.kind == SyntaxKind.ElseClause:
            pp = getattr(p, "parent", None)
            if pp is not None and pp.kind == SyntaxKind.IfGenerate:
                pkey = _ifgen_key(pp)
                if pkey in recs:
                    recs[pkey]["chain"] = key
                    chained.add(key)

    def emit(key):
        rec = recs[key]
        tm, em = rec["then"], rec["else"]
        holder = tm if tm is not None else em
        cond = None
        if holder is not None and holder.conditionExpression is not None:
            cond = convert_sym_expr(sm, holder.conditionExpression)
        then_body = convert_members_sym(sm, tm) if tm is not None else []
        if "chain" in rec:
            els = [emit(rec["chain"])]
        elif em is not None:
            els = convert_members_sym(sm, em)
        else:
            els = None
        return {
            "kind": "GenerateIf",
            "span": range_span(sm, getattr(rec["syntax"], "sourceRange",
                                           None)),
            "label": (tm.name or None) if tm is not None else None,
            "else_label": (em.name or None) if em is not None else None,
            "cond": cond,
            "then": then_body,
            "else": els,
        }

    return [emit(k) for k in order if k not in chained]


# --- symbolic member routing ----------------------------------------------

def convert_members_sym(sm, scope):
    """Members of a generate block (or nested scope) -> flat node list in
    source order. Genvar-local parameter shadows are skipped."""
    out = []
    members = list(scope)
    i = 0
    while i < len(members):
        m = members[i]
        try:
            k = str(m.kind).split(".")[-1]
            if k == "Parameter" and m.name in _SYM.genvars:
                i += 1
                continue
            if k == "GenerateBlock":
                run = []
                j = i
                while j < len(members) and \
                        str(members[j].kind).split(".")[-1] == \
                        "GenerateBlock" and \
                        _ifgen_of(members[j].syntax)[0] is not None:
                    run.append(members[j])
                    j += 1
                if run:
                    out.extend(convert_generate_ifs(sm, run))
                    i = j
                    continue
                out.append(unsupported(sm, m,
                                       "GenerateBlockSymbol:unconditional"))
                i += 1
                continue
            out.append(_convert_member_sym(sm, m, k))
            i += 1
        except Exception as exc:
            out.append(internal_error(exc))
            i += 1
    return [d for d in out if d is not None]


def _convert_member_sym(sm, m, k):
    """One non-if-generate member -> node or None (silently skipped)."""
    if k == "Parameter":
        return convert_param_sym(sm, m)
    if k == "Genvar":
        return None  # captured by the owning GenerateFor
    if k == "StatementBlock":
        return None
    if k == "TransparentMember":
        w = m.wrapped
        if type(w).__name__ == "EnumValueSymbol":
            register_enum(sm, w.type)
            return None
        return unsupported(sm, m, "TransparentMemberSymbol:"
                           + type(w).__name__)
    if k == "Variable":
        return convert_var_sym(sm, m)
    if k == "Net":
        return convert_net_sym(sm, m)
    if k == "ProceduralBlock":
        return convert_procedural_block(sm, m)
    if k == "ContinuousAssign":
        return convert_continuous_assign(sm, m)
    if k == "GenerateBlockArray":
        return convert_generate_for(sm, m)
    if k == "TypeAlias":
        try:
            if _sym_enum_width(m.declaredType.type) is not None:
                register_enum(sm, m.declaredType.type)
                return None
        except Exception:
            pass
        return unsupported(sm, m, type(m).__name__ + ":" + k)
    return unsupported(sm, m, type(m).__name__ + ":" + k)


def convert_module_sym(sm, inst):
    """Top module -> symbolic Module node (schema sv-0.2)."""
    body = inst.body
    _SYM.scope = body
    span = sym_span(sm, body) or sym_span(sm, inst)

    port_names = set()
    for m in body:
        if str(m.kind) == "SymbolKind.Port":
            port_names.add(m.name)

    imports = []
    params = []
    ports = []
    decls = []
    processes = []
    generates = []
    others = []

    members = list(body)
    i = 0
    while i < len(members):
        m = members[i]
        try:
            k = str(m.kind).split(".")[-1]
            if k == "Port":
                ports.append(convert_port_sym(sm, m))
            elif k in ("Variable", "Net"):
                if m.name in port_names:
                    i += 1
                    continue
                decls.append(convert_var_sym(sm, m) if k == "Variable"
                             else convert_net_sym(sm, m))
            elif k == "Parameter":
                params.append(convert_param_sym(sm, m))
            elif k == "ProceduralBlock":
                processes.append(convert_procedural_block(sm, m))
            elif k == "ContinuousAssign":
                processes.append(convert_continuous_assign(sm, m))
            elif k == "GenerateBlockArray":
                generates.append(convert_generate_for(sm, m))
            elif k == "GenerateBlock":
                run = []
                j = i
                while j < len(members) and \
                        str(members[j].kind).split(".")[-1] == \
                        "GenerateBlock" and \
                        _ifgen_of(members[j].syntax)[0] is not None:
                    run.append(members[j])
                    j += 1
                if run:
                    generates.extend(convert_generate_ifs(sm, run))
                    i = j
                    continue
                others.append(unsupported(sm, m,
                                          "GenerateBlockSymbol:unconditional"))
            elif k == "WildcardImport":
                pkg = getattr(m, "packageName", None) or ""
                _SYM.packages.add(pkg)
                imports.append({
                    "kind": "Import",
                    "span": sym_span(sm, m),
                    "package": pkg,
                    "name": "*",
                })
            elif k == "ExplicitImport":
                pkg = getattr(m, "packageName", None) or ""
                _SYM.packages.add(pkg)
                imports.append({
                    "kind": "Import",
                    "span": sym_span(sm, m),
                    "package": pkg,
                    "name": getattr(m, "importName", None) or m.name,
                })
            else:
                d = _convert_member_sym(sm, m, k)
                if d is not None:
                    others.append(d)
        except Exception as exc:
            others.append(internal_error(exc))
        i += 1

    return {
        "kind": "Module",
        "span": span,
        "name": inst.name,
        "imports": imports,
        "params": params,
        "types": _SYM.enum_nodes,
        "ports": ports,
        "decls": decls,
        "processes": processes,
        "generates": generates,
        "others": others,
    }


def process_symbolic(top, sources, incdirs, out_path):
    """`--top` mode: compile all sources as ONE slang compilation (name
    resolution across packages/files) and emit the top module in the
    extended symbolic vocabulary as one sv-0.2 envelope."""
    global _SYM
    source_map = {}
    file_entries = []
    for p in sources:
        try:
            with open(p, "rb") as f:
                data = f.read()
        except OSError as e:
            raise ExtractError("%s: cannot read: %s" % (p, e))
        try:
            data.decode("utf-8")
        except UnicodeDecodeError as e:
            raise ExtractError("%s: not valid UTF-8: %s" % (p, e))
        source_map[os.path.normpath(p)] = data
        file_entries.append({
            "path": rel_posix(p),
            "sha256": hashlib.sha256(data).hexdigest(),
        })

    if incdirs:
        sm_obj = pyslang.SourceManager()
        popt = pyslang.parsing.PreprocessorOptions()
        popt.additionalIncludePaths = list(incdirs)
        bag = pyslang.Bag([popt])
        tree = SyntaxTree.fromFiles(list(sources), sm_obj, bag)
    else:
        tree = SyntaxTree.fromFiles(list(sources))
    comp = Compilation()
    comp.addSyntaxTree(tree)
    sm = tree.sourceManager

    inst = None
    for cand in comp.getRoot().topInstances:
        if cand.name == top:
            inst = cand
            break
    if inst is None:
        raise ExtractError(
            "--top %s: no such module among top instances (%s)"
            % (top, ", ".join(c.name for c in comp.getRoot().topInstances)))

    nerr = sum(1 for d in comp.getAllDiagnostics() if d.isError())
    if nerr:
        print("warning: %d compilation error diagnostic(s); extracting "
              "anyway (out-of-vocabulary nodes become Unsupported)" % nerr,
              file=sys.stderr)

    _SYM = SymCtx(comp, sm, source_map)
    try:
        try:
            module = convert_module_sym(sm, inst)
        except Exception as exc:
            module = internal_error(exc)
        envelope = {
            "schema_version": SYM_SCHEMA_VERSION,
            "language": "systemverilog",
            "frontend": {"name": FRONTEND["name"],
                         "family": FRONTEND["family"]},
            "mode": "symbolic",
            "top": top,
            "source_files": file_entries,
            "packages": sorted(_SYM.packages - {""}),
            "design": {"kind": "Design", "modules": [module], "others": []},
            "lean_blocks": [],
        }
    finally:
        _SYM = None

    if out_path is None:
        # Default: next to the source file that defines the top module.
        out_path = sources[-1] + ".json"
        try:
            deffile = os.path.normpath(sm.getFileName(inst.location))
            for p in sources:
                if os.path.normpath(p) == deffile:
                    out_path = p + ".json"
                    break
        except Exception:
            pass
    with open(out_path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(envelope, f, indent=2)
        f.write("\n")
    return out_path


SYM_SCHEMA_VERSION = "sv-0.2"


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
        "frontend": {"name": FRONTEND["name"], "family": FRONTEND["family"]},
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
        description="Extract SystemVerilog sources to envelope JSON. "
        "Default (single-file M0 mode): each file.sv is compiled alone and "
        "written as <file>.sv.json next to the source (schema sv-0.1). "
        "With --top: ALL sources are compiled as ONE slang compilation "
        "(cross-file name resolution) and the named top module is emitted "
        "in the symbolic vocabulary (schema sv-0.2) — parameters and "
        "generate constructs stay symbolic, never folded/unrolled.",
    )
    parser.add_argument("sources", nargs="+", metavar="file.sv")
    parser.add_argument("--top", metavar="MODULE", default=None,
                        help="symbolic mode: emit this top module from one "
                        "multi-file compilation")
    parser.add_argument("-I", dest="incdirs", action="append", default=[],
                        metavar="DIR", help="`include search dir "
                        "(symbolic mode only)")
    parser.add_argument("-o", dest="out", default=None, metavar="OUT.json",
                        help="symbolic mode: output path (default: next to "
                        "the file defining the top module)")
    args = parser.parse_args(argv)

    try:
        if args.top is not None:
            out = process_symbolic(args.top, args.sources, args.incdirs,
                                   args.out)
            print(out)
        else:
            if args.incdirs or args.out:
                raise ExtractError("-I/-o require --top (symbolic mode)")
            for src in args.sources:
                process_file(src)
    except ExtractError as e:
        print("error: %s" % e, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
