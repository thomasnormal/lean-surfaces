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
    VisitAction,
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
    BinaryOperator.Multiply: "*",
    BinaryOperator.Divide: "/",
    BinaryOperator.Mod: "%",
    BinaryOperator.Power: "**",
    BinaryOperator.LogicalShiftLeft: "<<",
    BinaryOperator.LogicalShiftRight: ">>",
    BinaryOperator.ArithmeticShiftLeft: "<<<",
    BinaryOperator.ArithmeticShiftRight: ">>>",
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
    # wildcard comparisons and logical ops. All yield 1-bit results.
    BinaryOperator.CaseEquality: "===",
    BinaryOperator.CaseInequality: "!==",
    BinaryOperator.WildcardEquality: "==?",
    BinaryOperator.WildcardInequality: "!=?",
    BinaryOperator.LogicalAnd: "&&",
    BinaryOperator.LogicalOr: "||",
}
COMPARISON_SYMS = ("==", "!=", "<", "<=", ">", ">=", "===", "!==", "==?", "!=?")
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
    UnaryOperator.Plus: "+",
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
_DIV_CONTEXT = 0


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
    """(width, None) for an M0-supported 4-state integral type.

    Signedness is retained as envelope metadata; it does not change the
    admitted scalar or descending packed-vector shape.
    """
    try:
        if not t.isFourState:
            return None, "2state"
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
    integral scalar, predefined integer, or `[W-1:0]` packed vector of a
    scalar type, signed or unsigned, 4-state or 2-state. Other type shapes
    return `(None, None, reason)`."""
    try:
        ct = t.canonicalType
        cname = type(ct).__name__
        if cname == "ScalarType":
            return 1, (not t.isFourState), None
        if cname == "PredefinedIntegerType":
            return ct.bitWidth, (not t.isFourState), None
        if cname == "EnumType" and _SYM is None:
            return type_width_2s(ct.baseType)
        if cname == "PackedArrayType":
            w = ct.bitWidth
            elem = ct.elementType.canonicalType
            if type(elem).__name__ == "ScalarType":
                return w, (not t.isFourState), None
            return None, None, "range"
        if cname in ("PackedStructType", "PackedUnionType"):
            if getattr(ct, "isTagged", False):
                return None, None, "type"
            return ct.bitWidth, (not t.isFourState), None
        return None, None, "type"
    except Exception:
        return None, None, "type"


def is_integral_type_alias(symbol):
    """Admitted bound typedefs have no runtime effect on the legacy path."""
    if str(symbol.kind) != "SymbolKind.TypeAlias":
        return False
    try:
        _, _, reason = type_width_2s(symbol.declaredType.type)
        return reason is None or _fixed_query_dimensions(symbol.declaredType.type) is not None
    except Exception:
        return False


def is_bound_enum_member(symbol):
    """An admitted enum's transparent member introduces no runtime binding."""
    if str(symbol.kind) != "SymbolKind.TransparentMember":
        return False
    try:
        member = symbol.wrapped
        if str(member.kind) != "SymbolKind.EnumValue":
            return False
        width, _, reason = type_width_2s(member.type)
        value = member.value.value
        return (reason is None and type(value).__name__ == "SVInt"
                and value.bitWidth == width)
    except Exception:
        return False


def contains_bound_enum(comp):
    """Retain enum admission evidence before nominal information is erased."""
    found = False

    def inspect(node):
        nonlocal found
        sv_type = getattr(node, "type", None)
        if str(getattr(node, "kind", "")) == "SymbolKind.TypeAlias":
            sv_type = node.declaredType.type
        canonical = getattr(sv_type, "canonicalType", None)
        if type(canonical).__name__ == "EnumType":
            found = True

    comp.getRoot().visit(inspect)
    for unit in comp.getCompilationUnits():
        unit.visit(inspect)
    return found


def contains_admitted_type_alias(comp):
    """Keep frontend errors visible when compile-time aliases are erased."""
    found = False

    def inspect(node):
        nonlocal found
        if (str(getattr(node, "kind", "")) == "SymbolKind.TypeAlias"
                and is_integral_type_alias(node)):
            found = True

    comp.getRoot().visit(inspect)
    for unit in comp.getCompilationUnits():
        unit.visit(inspect)
    return found


def signed_metadata(node, sv_type):
    """Record signedness without changing existing unsigned envelopes."""
    if sv_type.isSigned:
        node["signed"] = True
    return node


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
    if _SYM is None and _contains_guarded_call(e):
        return None
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


def _contains_guarded_call(expression):
    """Keep call admission and diagnostic provenance through conversions."""
    found = False

    def inspect(node):
        nonlocal found
        if (type(node).__name__ == "CallExpression" and node.isSystemCall
                and node.subroutineName in
                ("$bits", *BIT_QUERY_CALLS, *SIGNING_CALLS, *DIMENSION_QUERY_CALLS)):
            found = True
            return VisitAction.Skip

    expression.visit(inspect)
    return found


def _bits_argument_source_ok(expression):
    """Effectful query operands remain outside the licensed-confirmed tier."""
    pure = True

    def inspect(node):
        nonlocal pure
        kind = type(node).__name__
        if kind == "CallExpression" and _fixed_bits_query_width(node) is not None:
            return VisitAction.Skip
        if kind == "CallExpression" and _signing_call(node):
            pure = pure and _signing_signature_ok(node)
            return
        pure = pure and not getattr(node, "bad", False) and kind in (
            "DataTypeExpression", "IntegerLiteral", "UnbasedUnsizedIntegerLiteral",
            "StringLiteral", "RealLiteral", "NamedValueExpression",
            "ConversionExpression", "UnaryExpression", "BinaryExpression",
            "ConditionalExpression", "ConcatenationExpression",
            "ReplicationExpression", "ElementSelectExpression",
            "RangeSelectExpression", "MemberAccessExpression",
        )
        if kind == "UnaryExpression":
            pure = pure and node.op not in (
                UnaryOperator.Preincrement, UnaryOperator.Predecrement,
                UnaryOperator.Postincrement, UnaryOperator.Postdecrement,
            )

    expression.visit(inspect)
    return pure


def _fixed_bits_query_width(expression):
    """Fixed bitstream queries inspect bound types, never operand values."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or expression.bad or not expression.isSystemCall
                or expression.subroutineName != "$bits"
                or len(expression.arguments) != 1):
            return None
        argument = expression.arguments[0]
        if (argument.bad or not argument.type.isFixedSize
                or not argument.type.isBitstreamType()
                or expression.type.bitWidth != 32
                or not expression.type.isSigned
                or not _bits_argument_source_ok(argument)):
            return None
        return argument.type.bitstreamWidth
    except Exception:
        return None


def _convert_fixed_bits_query(sm, expression):
    width = _fixed_bits_query_width(expression)
    if width is None:
        return unsupported(sm, expression)
    return {
        "kind": "Literal", "span": node_span(sm, expression),
        "width": 32, "bits": format(width & 0xffffffff, "032b"),
        "signed": True, "fixed_bits_query": True,
    }


BIT_QUERY_CALLS = ("$countbits", "$countones", "$onehot", "$onehot0", "$isunknown")
SIGNING_CALLS = ("$signed", "$unsigned")
DIMENSION_QUERY_CALLS = (
    "$size", "$high", "$left", "$right", "$low", "$increment",
    "$dimensions", "$unpacked_dimensions",
)


def _signing_call(expression):
    return (type(expression).__name__ == "CallExpression"
            and not expression.bad and expression.isSystemCall
            and expression.subroutineName in SIGNING_CALLS)


def _signing_signature_ok(expression):
    arguments = list(expression.arguments)
    if len(arguments) != 1:
        return False
    argument = arguments[0]
    return (argument.type.isIntegral and expression.type.isIntegral
            and argument.type.bitWidth == expression.type.bitWidth
            and expression.type.isSigned == (expression.subroutineName == "$signed")
            and expression.type.isFourState == argument.type.isFourState)


def _convert_signing_call(sm, expression):
    if not _signing_signature_ok(expression):
        return unsupported(sm, expression, "SigningCast:signature")
    operand = _convert_expr(sm, expression.arguments[0])
    operand.pop("signed", None)
    operand["signing_cast"] = expression.subroutineName
    operand["span"] = node_span(sm, expression)
    return signed_metadata(operand, expression.type)


def _bit_query_call(expression):
    try:
        return (type(expression).__name__ == "CallExpression"
                and not expression.bad and expression.isSystemCall
                and expression.subroutineName in BIT_QUERY_CALLS)
    except Exception:
        return False


def _clog2_call(expression):
    try:
        return (type(expression).__name__ == "CallExpression"
                and not expression.bad and expression.isSystemCall
                and expression.subroutineName == "$clog2")
    except Exception:
        return False


def _convert_clog2(sm, expression):
    """Fold a pure, frontend-bound `$clog2` call to its signed int result."""
    try:
        arguments = list(expression.arguments)
    except Exception:
        return unsupported(sm, expression, "CallExpression:$clog2:signature")
    if len(arguments) != 1:
        return unsupported(sm, expression, "CallExpression:$clog2:arity")
    argument = arguments[0]
    if not argument.type.isIntegral or not _case_source_expression_ok(argument):
        return unsupported(sm, expression, "CallExpression:$clog2:argument")
    literal = const_literal(sm, expression)
    if literal is None:
        return unsupported(sm, expression, "CallExpression:$clog2:dynamic")
    literal["signed"] = True
    literal["fixed_clog2"] = True
    return literal


def _dimension_query_call(expression):
    try:
        return (type(expression).__name__ == "CallExpression"
                and not expression.bad and expression.isSystemCall
                and expression.subroutineName in DIMENSION_QUERY_CALLS)
    except Exception:
        return False


def _time_call(expression):
    """A zero-argument `$time` query in the time-zero self-check slice."""
    try:
        return (type(expression).__name__ == "CallExpression"
                and not expression.bad and expression.isSystemCall
                and expression.subroutineName == "$time"
                and len(expression.arguments) == 0
                and expression.type.isIntegral)
    except Exception:
        return False


def _convert_time_call(sm, expression):
    if not _time_call(expression):
        return unsupported(sm, expression, "CallExpression:$time")
    return {
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": expression.type.bitWidth,
        "bits": "0" * expression.type.bitWidth,
        "time_zero": True,
    }


def _fixed_query_dimensions(value_type):
    """Declared dimensions, unpacked first, for fixed integral bitstreams."""
    if not value_type.isFixedSize:
        return None
    dimensions = []
    unpacked = 0
    current = value_type.canonicalType
    while True:
        kind = type(current).__name__
        if kind in ("FixedSizeUnpackedArrayType", "PackedArrayType"):
            dimensions.append((current.range.left, current.range.right))
            unpacked += kind == "FixedSizeUnpackedArrayType"
            current = current.elementType.canonicalType
        elif kind in ("PredefinedIntegerType", "EnumType", "PackedStructType", "PackedUnionType"):
            if kind == "PackedUnionType" and current.isTagged:
                return None
            dimensions.append((current.bitWidth - 1, 0))
            break
        elif kind == "ScalarType":
            break
        else:
            return None
    return dimensions, unpacked


def _constant_dimension_selector(expression):
    """Use bound constants or static leaves, never an evaluation context."""
    constant = expression.constant
    if constant is not None:
        value = constant.value
    elif type(expression).__name__ in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
        value = expression.value
    elif (type(expression).__name__ == "NamedValueExpression"
          and str(expression.symbol.kind) in ("SymbolKind.Parameter", "SymbolKind.EnumValue")):
        value = expression.symbol.value.value
    else:
        return None
    if type(value).__name__ != "SVInt" or value.bitWidth != expression.type.bitWidth:
        return None
    if any(bit not in "01" for bit in svint_bits(value)):
        return None
    return int(value)


def _fixed_array_cell(sm, expression):
    """Return the lowered cell for a constant element of a one-dimensional
    fixed unpacked integral array.

    The self-check state is a map of vector-valued signals, not a general
    unpacked-array store.  A constant array element can nevertheless be
    represented exactly by giving each cell its own state name.  Dynamic
    indices, nested arrays, whole-array expressions, and initializers remain
    outside this deliberately narrow lowering and stay loud.
    """
    try:
        source = expression.value
        if type(source).__name__ != "NamedValueExpression":
            return None
        if str(source.symbol.kind) not in ("SymbolKind.Variable", "SymbolKind.Net"):
            return None
        source_type = source.type
        array_type = source_type.canonicalType
        if type(array_type).__name__ != "FixedSizeUnpackedArrayType":
            return None
        element_type = array_type.elementType
        if type(element_type.canonicalType).__name__ == "FixedSizeUnpackedArrayType":
            return None
        width, two_state, reason = type_width_2s(element_type)
        if width is None or reason is not None:
            return None
        index = (expression.selector if type(expression).__name__ ==
                 "ElementSelectExpression" else None)
        if index is None:
            return None
        position = _constant_dimension_selector(index)
        if position is None:
            return None
        left, right = int(array_type.range.left), int(array_type.range.right)
        lo, hi = min(left, right), max(left, right)
        if position < lo or position > hi:
            return None
        return f"{source.symbol.name}[{position}]", width, two_state
    except Exception:
        return None


def _fixed_array_pattern_assignment(sm, expr):
    """Lower one exact positional assignment to a fixed-array's cells.

    The self-check state has no aggregate store: declarations of a narrow
    one-dimensional fixed unpacked array are already expanded to names such
    as ``a[0]``.  A whole-array assignment can therefore use the same state
    by expanding an exact positional pattern into a block of per-cell
    assignments.  Keep the lowering deliberately strict.  The pattern must
    be simple and exact-length, every element must be a pure integral
    expression, and no element may read the destination array.  The last
    guard preserves the source-level rule that the complete RHS is evaluated
    before any destination cell is updated; without it, a later element
    could observe an earlier lowered write.
    """
    try:
        if type(expr).__name__ != "AssignmentExpression":
            return None
        if expr.op is not None or expr.timingControl is not None:
            return None
        lhs = expr.left
        if type(lhs).__name__ != "NamedValueExpression":
            return None
        if str(lhs.symbol.kind) != "SymbolKind.Variable":
            return None
        lhs_type = lhs.type.canonicalType
        if type(lhs_type).__name__ != "FixedSizeUnpackedArrayType":
            return None
        element_type = lhs_type.elementType
        if type(element_type.canonicalType).__name__ == "FixedSizeUnpackedArrayType":
            return None
        if type(element_type.canonicalType).__name__ in ("PackedStructType", "PackedUnionType"):
            return None
        element_width, element_two, reason = type_width_2s(element_type)
        if element_width is None or reason is not None:
            return None
        pattern = expr.right
        if type(pattern).__name__ != "SimpleAssignmentPatternExpression":
            return None
        elements = list(pattern.elements)
        left, right = int(lhs_type.range.left), int(lhs_type.range.right)
        count = abs(left - right) + 1
        if count > 1024 or len(elements) != count:
            return None
        target_name = lhs.symbol.name
        converted = []
        for element in elements:
            if not _case_source_expression_ok(element):
                return None
            # A pure read of the destination would see a different value
            # after the first lowered cell write.  Reject that aliasing shape
            # instead of silently changing aggregate-assignment semantics.
            reads_target = False
            def inspect(node):
                nonlocal reads_target
                if type(node).__name__ == "NamedValueExpression":
                    try:
                        reads_target = reads_target or node.symbol.name == target_name
                    except Exception:
                        reads_target = True
            element.visit(inspect)
            if reads_target:
                return None
            value = convert_expr(sm, element)
            if (value is None or value.get("kind") == "Unsupported"
                    or width_of(value) != element_width
                    or not _case_expression_ok(value)):
                return None
            if element_two:
                value = squash2_wrap(value, element_width)
            converted.append(value)
        step = 1 if right >= left else -1
        stmts = []
        for position, value in zip(range(left, right + step, step), converted):
            target = {
                "kind": "Ident",
                "span": node_span(sm, lhs),
                "width": element_width,
                "name": f"{target_name}[{position}]",
            }
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": target,
                "value": value,
            })
        return {
            "kind": "Block",
            "span": node_span(sm, expr),
            "stmts": stmts,
        }
    except Exception:
        return None


def _convert_dimension_query(sm, expression):
    """Fold fixed array metadata without evaluating the queried operand."""
    try:
        arguments = list(expression.arguments)
    except Exception:
        return unsupported(sm, expression, "CallExpression:dimension:signature")
    count_query = expression.subroutineName in ("$dimensions", "$unpacked_dimensions")
    if len(arguments) not in ((1,) if count_query else (1, 2)):
        return unsupported(sm, expression, "CallExpression:dimension:arity")
    argument = arguments[0]
    shape = _fixed_query_dimensions(argument.type)
    if shape is None or not _bits_argument_source_ok(argument):
        return unsupported(sm, expression, "CallExpression:dimension:argument")
    dimensions, unpacked = shape
    if count_query:
        value = len(dimensions) if expression.subroutineName == "$dimensions" else unpacked
    else:
        dimension = 1
        if len(arguments) == 2:
            selector = arguments[1]
            if not selector.type.isIntegral or not _bits_argument_source_ok(selector):
                return unsupported(sm, expression, "CallExpression:dimension:selector")
            dimension = _constant_dimension_selector(selector)
            if dimension is None:
                return unsupported(sm, expression, "CallExpression:dimension:dynamic")
        if not 1 <= dimension <= len(dimensions):
            return unsupported(sm, expression, "CallExpression:dimension:index")
        left, right = dimensions[dimension - 1]
        value = {
            "$size": abs(left - right) + 1,
            "$high": max(left, right),
            "$left": left,
            "$right": right,
            "$low": min(left, right),
            "$increment": 1 if left >= right else -1,
        }[expression.subroutineName]
    return {
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": 32,
        "bits": format(value & 0xffffffff, "032b"),
        "signed": True,
        "fixed_dimension_query": expression.subroutineName,
    }


def _convert_bit_query(sm, expression):
    name = expression.subroutineName
    arguments = list(expression.arguments)
    count_query = name in ("$countbits", "$countones")
    valid_arity = len(arguments) >= 2 if name == "$countbits" else len(arguments) == 1
    if (not valid_arity or expression.type.bitWidth != (32 if count_query else 1)
            or expression.type.isSigned != count_query):
        return unsupported(sm, expression, "BitQuery:signature")
    if any(type_width_2s(argument.type)[0] is None for argument in arguments):
        return unsupported(sm, expression, "BitQuery:argument-type")
    return signed_metadata({
        "kind": "BitQuery", "span": node_span(sm, expression),
        "width": expression.type.bitWidth, "op": name,
        "operand": convert_expr(sm, arguments[0]),
        "controls": [convert_expr(sm, argument) for argument in arguments[1:]],
    }, expression.type)


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
    if cname == "ConversionExpression":
        return _convert_conversion_expr(sm, e)
    if cname == "NamedValueExpression":
        return _convert_named_value_expr(sm, e)
    if cname in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
        return _convert_integer_expr(sm, e, cname)
    if cname == "StringLiteral":
        return _convert_string_expr(sm, e)
    if cname == "UnaryExpression":
        return _convert_unary_expr(sm, e)
    if cname == "BinaryExpression":
        return _convert_binary_expr(sm, e)
    if cname == "ConditionalExpression":
        return _convert_conditional_expr(sm, e)
    if cname == "ConcatenationExpression":
        return _convert_concat_expr(sm, e)
    if _SYM is None and cname == "MemberAccessExpression":
        member = _packed_struct_member(sm, e)
        if member is not None:
            base, width, offset, _two_state = member
            return {
                "kind": "SelectRead",
                "span": node_span(sm, e),
                "width": width,
                "value": _convert_expr(sm, e.value),
                "index": {
                    "kind": "Literal",
                    "span": node_span(sm, e),
                    "width": 32,
                    "bits": format(offset, "032b"),
                },
                "index_signed": False,
                "descending": False,
            }
    if _SYM is None and cname in ("ElementSelectExpression", "RangeSelectExpression"):
        return _convert_selected_read(sm, e, cname)
    if cname == "CallExpression":
        if _SYM is None:
            if _clog2_call(e):
                return _convert_clog2(sm, e)
            if _dimension_query_call(e):
                return _convert_dimension_query(sm, e)
            if _time_call(e):
                return _convert_time_call(sm, e)
            if _signing_call(e):
                return _convert_signing_call(sm, e)
            if _bit_query_call(e):
                return _convert_bit_query(sm, e)
            return _convert_fixed_bits_query(sm, e)
        return _convert_sym_call_expr(sm, e)
    if _SYM is not None and cname in (
        "ElementSelectExpression", "RangeSelectExpression", "ReplicationExpression"
    ):
        return _convert_sym_select_expr(sm, e, cname)
    return unsupported(sm, e)


def _convert_conversion_expr(sm, e):
    """Lower elaborated resizing after context signedness has propagated."""
    kind = e.conversionKind
    if kind == ConversionKind.Explicit:
        return _convert_integral_cast(sm, e)
    if kind not in (ConversionKind.Implicit, ConversionKind.Propagated):
        return unsupported(sm, e, "ConversionExpression:" + str(kind).split(".")[-1])
    ow, tw = e.operand.type.bitWidth, e.type.bitWidth
    state_squash = e.operand.type.isFourState and not e.type.isFourState
    if _SYM is not None and _DIV_CONTEXT and not _SYM.symctx:
        node = _sym_conversion(sm, e, ow, tw, state_squash)
        if node is not None:
            return node
    if ow == tw:
        if state_squash:
            return {
                "kind": "Squash2",
                "span": node_span(sm, e),
                "width": tw,
                "operand": _convert_expr(sm, e.operand),
            }
        return _convert_expr(sm, e.operand)
    if _SYM is not None:
        node = _sym_conversion(sm, e, ow, tw, state_squash)
        if node is not None:
            return node
    lit = const_literal(sm, e)
    if lit is not None:
        return lit
    try:
        resizable = e.operand.type.isIntegral and e.type.isIntegral
        signed = e.operand.type.isSigned and e.type.isSigned
    except Exception:
        resizable = False
        signed = False
    if not resizable or (signed and _SYM is not None):
        return unsupported(sm, e, "ConversionExpression:width")
    inner = _convert_expr(sm, e.operand)
    if state_squash:
        inner = {
            "kind": "Squash2",
            "span": node_span(sm, e),
            "width": ow,
            "operand": inner,
        }
    return {
        "kind": "SignedResize" if signed else "Resize",
        "span": node_span(sm, e),
        "width": tw,
        "operand": inner,
    }


def _convert_integral_cast(sm, expr):
    """Integral casts resize using the operand's self-determined signedness.
    Nonintegral/exotic types and symbolic casts remain loud."""
    source_width, _, source_reason = type_width_2s(expr.operand.type)
    target_width, two_state, target_reason = type_width_2s(expr.type)
    if _SYM is not None or source_reason is not None or target_reason is not None:
        return unsupported(sm, expr, "ConversionExpression:Explicit")
    operand = _convert_expr(sm, expr.operand)
    if source_width != target_width:
        operand = {
            "kind": "SignedResize" if expr.operand.type.isSigned else "Resize",
            "span": node_span(sm, expr),
            "width": target_width,
            "operand": operand,
        }
    if two_state and expr.operand.type.isFourState:
        operand = squash2_wrap(operand, target_width)
    return operand


def _convert_named_value_expr(sm, e):
    sym = e.symbol
    skind = str(sym.kind).split(".")[-1]
    if _SYM is not None:
        node = _sym_named_value(sm, e, sym, skind)
        if node is not None:
            return node
    if _SYM is None and skind == "EnumValue":
        return _convert_enum_member_expr(sm, e)
    if skind not in ("Variable", "Net"):
        return unsupported(sm, e, "NamedValueExpression:" + skind)
    width, _two, reason = type_width_2s(e.type)
    if width is None and _SYM is not None:
        enum_width = _sym_enum_width(e.type)
        if enum_width is not None:
            width = enum_width
        elif reason == "range":
            multidim_width = _multidim_width(e.type)
            if multidim_width is not None:
                width = multidim_width
    if width is None:
        if reason == "type" and not getattr(e.type, "isFourState", True):
            reason = "2state"
        return unsupported(sm, e, "NamedValueExpression:" + reason)
    return signed_metadata({
        "kind": "Ident",
        "span": node_span(sm, e),
        "width": width,
        "name": sym.name,
    }, e.type)


def _convert_enum_member_expr(sm, expr):
    """Preserve the exact, already-bound integral enumeration value."""
    width, _, reason = type_width_2s(expr.type)
    try:
        value = expr.symbol.value.value
        if (reason is not None or type(value).__name__ != "SVInt"
                or value.bitWidth != width):
            return unsupported(sm, expr, "NamedValueExpression:EnumValue")
        return signed_metadata({
            "kind": "Literal",
            "span": node_span(sm, expr),
            "width": width,
            "bits": svint_bits(value),
        }, expr.type)
    except Exception:
        return unsupported(sm, expr, "NamedValueExpression:EnumValue")


def _convert_integer_expr(sm, e, cname):
    if _SYM is not None:
        node = _sym_literal(sm, e, cname)
        if node is not None:
            return node
    value = e.value
    return {
        "kind": "Literal",
        "span": node_span(sm, e),
        "width": value.bitWidth,
        "bits": svint_bits(value),
    }


def _convert_string_expr(sm, e):
    try:
        data = e.value.encode("latin-1")
    except (UnicodeEncodeError, Exception):
        return unsupported(sm, e, "StringLiteral:encoding")
    width = e.type.bitWidth
    if width != (8 * len(data) if data else 8):
        return unsupported(sm, e, "StringLiteral:width")
    bits = "".join(format(byte, "08b") for byte in data) if data else "0" * 8
    return {
        "kind": "Literal",
        "span": node_span(sm, e),
        "width": width,
        "bits": bits,
    }


def _convert_unary_expr(sm, e):
    sym = UNARY_OPS.get(e.op)
    if sym is None:
        reduction = REDUCE_OPS.get(e.op)
        if reduction is not None:
            operand = _convert_expr(sm, e.operand)
            if _SYM is not None and _DIV_CONTEXT and not _SYM.symctx:
                operand = _division_self_operand(sm, e.operand, operand)
            if e.type.bitWidth != 1:
                return unsupported(sm, e, "UnaryExpression:width")
            return {
                "kind": "Reduce",
                "span": node_span(sm, e),
                "width": 1,
                "op": reduction,
                "operand": operand,
            }
    if sym is None:
        return unsupported(sm, e, "UnaryExpression:" + str(e.op).split(".")[-1])
    operand = _convert_expr(sm, e.operand)
    if sym == "!" and _DIV_CONTEXT and not _SYM.symctx:
        operand = _division_self_operand(sm, e.operand, operand)
    width = e.type.bitWidth
    operand_width = width_of(operand)
    ok = (width == 1) if sym == "!" else (operand_width is None or operand_width == width)
    if not ok:
        return unsupported(sm, e, "UnaryExpression:width")
    return {
        "kind": "Unary",
        "span": node_span(sm, e),
        "width": width,
        "op": sym,
        "operand": operand,
    }


def _binary_width_ok(sym, width, left_width, right_width):
    if sym == "**":
        return left_width is None or left_width == width
    if sym in ("<<", ">>", "<<<", ">>>"):
        return left_width is None or left_width == width
    if sym in COMPARISON_SYMS:
        return width == 1 and (
            left_width is None or right_width is None or left_width == right_width
        )
    if sym in LOGICAL_SYMS:
        return width == 1
    return (left_width is None or left_width == width) and (
        right_width is None or right_width == width
    )


def _division_self_operand(sm, expression, operand):
    return {"kind": "SignedResize" if expression.type.isSigned else "Resize",
            "span": node_span(sm, expression), "width": expression.type.bitWidth,
            "operand": operand}


def _convert_division_operand(sm, expression):
    global _DIV_CONTEXT
    previous = _DIV_CONTEXT
    _DIV_CONTEXT += 1
    try:
        return _convert_expr(sm, expression)
    finally:
        _DIV_CONTEXT = previous


def _convert_binary_expr(sm, e):
    sym = BINARY_OPS.get(e.op)
    if sym is None and _SYM is not None and _SYM.symctx:
        symbolic = SYM_BINARY_OPS.get(e.op)
        if symbolic is not None:
            return {
                "kind": "Binary",
                "span": node_span(sm, e),
                "width": _safe_width(e),
                "op": symbolic,
                "left": _convert_expr(sm, e.left),
                "right": _convert_expr(sm, e.right),
            }
    if sym is None:
        return unsupported(sm, e, "BinaryExpression:" + str(e.op).split(".")[-1])
    if sym in ("/", "%", "**", "<<", ">>", "<<<", ">>>") and _SYM is not None and not _SYM.symctx:
        left = _convert_division_operand(sm, e.left)
        right = _convert_division_operand(sm, e.right)
    else:
        left = _convert_expr(sm, e.left)
        right = _convert_expr(sm, e.right)
    if _DIV_CONTEXT and not _SYM.symctx and sym in (
            "==", "!=", "==?", "!=?", "<", "<=", ">", ">=", "&&", "||"):
        left = _division_self_operand(sm, e.left, left)
        right = _division_self_operand(sm, e.right, right)
    width = e.type.bitWidth
    if not _binary_width_ok(sym, width, width_of(left), width_of(right)):
        return unsupported(sm, e, "BinaryExpression:width")
    if sym == "/" and not (_SYM is not None and _SYM.symctx):
        if not (e.type.isIntegral and e.left.type.isIntegral and e.right.type.isIntegral):
            return unsupported(sm, e, "BinaryExpression:Divide-type")
        sym = "s/" if e.left.type.isSigned and e.right.type.isSigned else "u/"
    if sym == "%" and not (_SYM is not None and _SYM.symctx):
        if not (e.type.isIntegral and e.left.type.isIntegral and e.right.type.isIntegral):
            return unsupported(sm, e, "BinaryExpression:Mod-type")
        sym = "s%" if e.left.type.isSigned and e.right.type.isSigned else "u%"
    if sym == "**" and not (_SYM is not None and _SYM.symctx):
        if not (e.type.isIntegral and e.left.type.isIntegral and e.right.type.isIntegral):
            return unsupported(sm, e, "BinaryExpression:Power-type")
        sym = ("s" if e.left.type.isSigned else "u") + "**" + ("s" if e.right.type.isSigned else "u")
    if sym in ("<<", ">>", "<<<", ">>>") and not (_SYM is not None and _SYM.symctx):
        if not (e.type.isIntegral and e.left.type.isIntegral and e.right.type.isIntegral):
            return unsupported(sm, e, "BinaryExpression:Shift-type")
        sym = ("s" if e.left.type.isSigned else "u") + sym
    if sym in ORDER_CMP_SYMS:
        try:
            if e.left.type.isSigned and e.right.type.isSigned:
                sym = "s" + sym
        except Exception:
            return unsupported(sm, e, "BinaryExpression:signedness")
    return {
        "kind": "Binary",
        "span": node_span(sm, e),
        "width": width,
        "op": sym,
        "left": left,
        "right": right,
    }


def _convert_conditional_expr(sm, e):
    conds = e.conditions
    if len(conds) != 1:
        return unsupported(sm, e, "ConditionalExpression:multi")
    if conds[0].pattern is not None:
        return unsupported(sm, e, "ConditionalExpression:pattern")
    cond = _convert_expr(sm, conds[0].expr)
    if _DIV_CONTEXT and not _SYM.symctx:
        cond = _division_self_operand(sm, conds[0].expr, cond)
    then = _convert_expr(sm, e.left)
    els = _convert_expr(sm, e.right)
    width = e.type.bitWidth
    then_width, else_width = width_of(then), width_of(els)
    if (then_width is not None and then_width != width) or (
        else_width is not None and else_width != width
    ):
        return unsupported(sm, e, "ConditionalExpression:width")
    return {
        "kind": "Ternary",
        "span": node_span(sm, e),
        "width": width,
        "cond": cond,
        "then": then,
        "else": els,
    }


def _convert_concat_expr(sm, e):
    parts = [_convert_expr(sm, operand) for operand in e.operands]
    if _DIV_CONTEXT and not _SYM.symctx:
        parts = [_division_self_operand(sm, operand, converted)
                 for operand, converted in zip(e.operands, parts)]
    width = e.type.bitWidth
    widths = [width_of(part) for part in parts]
    if all(part_width is not None for part_width in widths) and sum(widths) != width:
        return unsupported(sm, e, "ConcatenationExpression:width")
    return {
        "kind": "Concat",
        "span": node_span(sm, e),
        "width": width,
        "parts": parts,
    }


def _canonical_packed_select_source(source_type):
    """Whether selected access still has the zero-based packed geometry.

    Whole-vector operations are range-independent, but the legacy selected
    read/write evaluator currently interprets an index as an LSB offset.
    Keep noncanonical packed ranges loud until that evaluator carries the
    declared left/right bounds explicitly.
    """
    try:
        ct = source_type.canonicalType
        if type(ct).__name__ != "PackedArrayType":
            return True
        return int(ct.range.left) == ct.bitWidth - 1 and int(ct.range.right) == 0
    except Exception:
        return False


def _packed_constant_index(sm, source_type, index):
    """Normalize an in-range constant packed label to an LVec offset."""
    try:
        ct = source_type.canonicalType
        if type(ct).__name__ != "PackedArrayType":
            return None
        position = _constant_dimension_selector(index)
        if position is None:
            return None
        left, right = int(ct.range.left), int(ct.range.right)
        lo, hi = min(left, right), max(left, right)
        if position < lo or position > hi:
            return None
        offset = position - right if left > right else right - position
        width = index.type.bitWidth
        if offset < 0 or offset >= ct.bitWidth or width <= 0:
            return None
        return {
            "kind": "Literal",
            "span": node_span(sm, index),
            "width": width,
            "bits": format(offset & ((1 << width) - 1), f"0{width}b"),
        }, False
    except Exception:
        return None


def _packed_struct_member(sm, expression):
    """Describe one direct integral field of a packed struct/union value."""
    try:
        if type(expression).__name__ != "MemberAccessExpression":
            return None
        base = expression.value
        if type(base).__name__ != "NamedValueExpression":
            return None
        aggregate = base.type.canonicalType
        if type(aggregate).__name__ not in ("PackedStructType", "PackedUnionType"):
            return None
        if getattr(aggregate, "isTagged", False):
            return None
        member = expression.member
        width, two_state, reason = type_width_2s(member.type)
        if width is None or reason is not None:
            return None
        offset = int(member.bitOffset)
        if offset < 0 or offset + width > aggregate.bitWidth:
            return None
        return base, width, offset, two_state
    except Exception:
        return None


def _convert_selected_read(sm, expr, expression_kind):
    if expression_kind == "ElementSelectExpression":
        cell = _fixed_array_cell(sm, expr)
        if cell is not None:
            name, width, _two_state = cell
            return signed_metadata({
                "kind": "Ident",
                "span": node_span(sm, expr),
                "width": width,
                "name": name,
            }, expr.type)
    source_type = expr.value.type
    _, _, source_reason = type_width_2s(source_type)
    canonical_kind = type(source_type.canonicalType).__name__
    if (source_reason is not None or not source_type.isFourState
            or canonical_kind not in ("PredefinedIntegerType", "PackedArrayType")
            or (not _canonical_packed_select_source(source_type)
                and expression_kind != "ElementSelectExpression")):
        return unsupported(sm, expr, expression_kind + ":source-type")
    descending = False
    if expression_kind == "ElementSelectExpression":
        index = expr.selector
    else:
        selection = str(expr.selectionKind).split(".")[-1]
        if selection not in ("Simple", "IndexedUp", "IndexedDown"):
            return unsupported(sm, expr, "RangeSelectExpression:" + selection)
        index = expr.right if selection == "Simple" else expr.left
        descending = selection == "IndexedDown"
    index_signed = bool(index.type.isSigned)
    converted_index = None
    if (expression_kind == "ElementSelectExpression"
            and canonical_kind == "PackedArrayType"
            and not _canonical_packed_select_source(source_type)):
        normalized = _packed_constant_index(sm, source_type, index)
        if normalized is None:
            return unsupported(sm, expr, expression_kind + ":source-type")
        converted_index, index_signed = normalized
    else:
        _, _, index_reason = type_width_2s(index.type)
        if index_reason is not None:
            return unsupported(sm, expr, expression_kind + ":index-type")
        converted_index = _convert_expr(sm, index)
    return {
        "kind": "SelectRead",
        "span": node_span(sm, expr),
        "width": expr.type.bitWidth,
        "value": _convert_expr(sm, expr.value),
        "index": converted_index,
        "index_signed": index_signed,
        "descending": descending,
    }


def _convert_sym_call_expr(sm, e):
    node = _sym_expr_syscall(sm, e)
    if node is not None:
        return node
    node = _sym_cast_call(sm, e)
    return node if node is not None else unsupported(sm, e)


def _convert_sym_select_expr(sm, e, cname):
    if cname == "ElementSelectExpression":
        with _SymPos():
            index = _convert_expr(sm, e.selector)
        return {
            "kind": "BitSel",
            "span": node_span(sm, e),
            "width": _safe_width(e),
            "value": _convert_expr(sm, e.value),
            "index": index,
        }
    if cname == "RangeSelectExpression":
        selection = str(e.selectionKind).split(".")[-1]
        if selection != "Simple":
            return unsupported(sm, e, "RangeSelectExpression:" + selection)
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
    with _SymPos():
        count = _convert_expr(sm, e.count)
    return {
        "kind": "Repl",
        "span": node_span(sm, e),
        "width": _safe_width(e),
        "count": count,
        "operand": _convert_expr(sm, e.concat),
    }


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
    if _DIV_CONTEXT and not _SYM.symctx:
        operand = _division_self_operand(sm, args[0], operand)
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


def _compound_rhs(expr):
    """Peel pyslang's synthetic read-modify-write expression from a compound
    assignment. The frontend may wrap it in a conversion for unsized literals.
    """
    candidate = expr
    while type(candidate).__name__ == "ConversionExpression":
        operand = getattr(candidate, "operand", None)
        if operand is None:
            return expr
        candidate = operand
    if type(candidate).__name__ == "BinaryExpression":
        left = candidate.left
        while type(left).__name__ == "ConversionExpression":
            operand = getattr(left, "operand", None)
            if operand is None:
                return expr
            left = operand
        if type(left).__name__ == "LValueReferenceExpression":
            return candidate.right
    return expr


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


def legacy_blocking_target(sm, lhs, concat_leaf=False):
    expression_kind = type(lhs).__name__
    if expression_kind == "MemberAccessExpression":
        member = _packed_struct_member(sm, lhs)
        if member is not None:
            _base, width, offset, two_state = member
            target = {
                "kind": "SelectTarget",
                "span": node_span(sm, lhs),
                "width": width,
                "value": convert_expr(sm, lhs.value),
                "index": {
                    "kind": "Literal",
                    "span": node_span(sm, lhs),
                    "width": 32,
                    "bits": format(offset, "032b"),
                },
                "index_signed": False,
                "descending": False,
                "two_state": two_state,
            }
            return target, True
    if expression_kind == "ElementSelectExpression":
        cell = _fixed_array_cell(sm, lhs)
        if cell is not None:
            name, width, two_state = cell
            target = {
                "kind": "Ident",
                "span": node_span(sm, lhs),
                "width": width,
                "name": name,
            }
            if concat_leaf:
                target["two_state"] = two_state
            return target, True
    if expression_kind == "ConcatenationExpression":
        parts = [legacy_blocking_target(sm, operand, True) for operand in lhs.operands]
        if not parts or not all(admitted for _, admitted in parts):
            return unsupported(sm, lhs, expression_kind + ":target-operand"), False
        return {
            "kind": "ConcatTarget",
            "span": node_span(sm, lhs),
            "width": lhs.type.bitWidth,
            "parts": [target for target, _ in parts],
        }, True
    if expression_kind not in ("ElementSelectExpression", "RangeSelectExpression"):
        target, admitted = ident_target(sm, lhs)
        if concat_leaf:
            width, two_state, reason = type_width_2s(lhs.type)
            if not admitted or reason is not None or width is None:
                return unsupported(sm, lhs, expression_kind + ":target-type"), False
            target["two_state"] = two_state
        return target, admitted
    base, admitted = ident_target(sm, lhs.value)
    source_width, _, source_reason = type_width_2s(lhs.value.type)
    canonical_kind = type(lhs.value.type.canonicalType).__name__
    if (not admitted or source_reason is not None or source_width is None
            or canonical_kind not in ("PredefinedIntegerType", "PackedArrayType")
            or (not _canonical_packed_select_source(lhs.value.type)
                and expression_kind != "ElementSelectExpression")):
        return unsupported(sm, lhs, expression_kind + ":target-source"), False
    descending = False
    if expression_kind == "ElementSelectExpression":
        index = lhs.selector
    else:
        selection = str(lhs.selectionKind).split(".")[-1]
        if selection not in ("Simple", "IndexedUp", "IndexedDown"):
            return unsupported(sm, lhs, expression_kind + ":target-selection"), False
        index = lhs.right if selection == "Simple" else lhs.left
        descending = selection == "IndexedDown"
    index_signed = bool(index.type.isSigned)
    if (expression_kind == "ElementSelectExpression"
            and canonical_kind == "PackedArrayType"
            and not _canonical_packed_select_source(lhs.value.type)):
        normalized = _packed_constant_index(sm, lhs.value.type, index)
        if normalized is None:
            return unsupported(sm, lhs, expression_kind + ":target-source"), False
        converted_index, index_signed = normalized
    else:
        _, _, index_reason = type_width_2s(index.type)
        converted_index = convert_expr(sm, index)
        if (index_reason is not None or not _case_source_expression_ok(index)
                or not _case_expression_ok(converted_index)):
            return unsupported(sm, lhs, expression_kind + ":target-index"), False
    if (not _case_source_expression_ok(index)
            or not _case_expression_ok(converted_index)):
        return unsupported(sm, lhs, expression_kind + ":target-index"), False
    return {
        "kind": "SelectTarget",
        "span": node_span(sm, lhs),
        "width": lhs.type.bitWidth,
        "value": base,
        "index": converted_index,
        "index_signed": index_signed,
        "descending": descending,
        "two_state": not lhs.type.isFourState,
    }, True


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
        return _convert_expression_stmt(sm, s)
    if cname == "VariableDeclStatement":
        return _convert_local_decl(sm, s)
    if cname == "EmptyStatement":
        return {"kind": "Empty", "span": node_span(sm, s)}
    if cname == "BreakStatement":
        return {"kind": "Break", "span": node_span(sm, s)}
    if cname == "ContinueStatement":
        return {"kind": "Continue", "span": node_span(sm, s)}

    if cname == "ForLoopStatement":
        if _SYM is not None:
            return unsupported(sm, s)
        initializers = []
        for init in s.initializers:
            converted = _convert_assignment_expr(sm, init)
            if (converted.get("kind") != "BlockingAssign"
                    or not _case_expression_ok(converted)):
                return unsupported(sm, s, "ForLoopStatement:initializer")
            initializers.append(converted)
        steps = []
        for step in s.steps:
            converted = _convert_for_step(sm, step)
            if (converted.get("kind") != "BlockingAssign"
                    or not _case_expression_ok(converted)):
                return unsupported(sm, s, "ForLoopStatement:step")
            steps.append(converted)
        if s.stopExpr is None:
            condition = {"kind": "Literal", "span": None, "width": 1, "bits": "1"}
        else:
            condition = convert_expr(sm, s.stopExpr)
            if (not _case_expression_ok(condition)
                    or not _case_source_expression_ok(s.stopExpr)):
                return unsupported(sm, s, "ForLoopStatement:condition")
        body = convert_stmt(sm, s.body)
        if contains_local_decl(body):
            return unsupported(sm, s, "ForLoopStatement:body-lifetime")
        return {
            "kind": "For",
            "span": node_span(sm, s),
            "initializers": initializers,
            "condition": condition,
            "steps": steps,
            "body": body,
        }

    if cname == "RepeatLoopStatement":
        if _SYM is not None:
            return unsupported(sm, s)
        width, _, reason = type_width_2s(s.count.type)
        if width is None or reason is not None or not _case_source_expression_ok(s.count):
            return unsupported(sm, s, "RepeatLoopStatement:count")
        body = convert_stmt(sm, s.body)
        if contains_local_decl(body):
            return unsupported(sm, s, "RepeatLoopStatement:body-lifetime")
        return {
            "kind": "Repeat",
            "span": node_span(sm, s),
            "count": convert_expr(sm, s.count),
            "count_signed": bool(s.count.type.isSigned),
            "body": body,
        }

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
        if _SYM is None and type(s.timing).__name__ == "DelayControl":
            return _convert_delay_statement(sm, s)
        if _SYM is None and type(s.timing).__name__ == "SignalEventControl":
            return _convert_wait_event_statement(sm, s)
        return unsupported(sm, s, "TimedStatement:" + type(s.timing).__name__)

    if cname == "CaseStatement" and _SYM is None:
        return _convert_ordinary_case(sm, s)

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


def _convert_delay_statement(sm, statement):
    expression = statement.timing.expr
    if type(expression).__name__ != "IntegerLiteral" or not expression.type.isIntegral:
        return unsupported(sm, statement, "TimedStatement:DelayControl:expression")
    bits = svint_bits(expression.value)
    if not bits or any(bit not in "01" for bit in bits):
        return unsupported(sm, statement, "TimedStatement:DelayControl:unknown")
    if expression.type.isSigned and bits[0] == "1":
        return unsupported(sm, statement, "TimedStatement:DelayControl:negative")
    amount = int(bits, 2)
    if amount >= 1 << 64:
        return unsupported(sm, statement, "TimedStatement:DelayControl:range")
    return {
        "kind": "Delay",
        "span": node_span(sm, statement),
        "amount": amount,
        "body": convert_stmt(sm, statement.stmt),
    }


def _convert_wait_event_statement(sm, statement):
    timing = statement.timing
    if timing.edge not in (EdgeKind.PosEdge, EdgeKind.NegEdge, EdgeKind.None_):
        return unsupported(
            sm, statement, "SignalEventControl:" + str(timing.edge).split(".")[-1]
        )
    if timing.iffCondition is not None:
        return unsupported(sm, statement, "SignalEventControl:iff")
    signal = convert_expr(sm, timing.expr)
    if signal.get("kind") != "Ident" or signal.get("width") != 1:
        return unsupported(sm, statement, "SignalEventControl:clock")
    wait = {
        "kind": "WaitEvent",
        "span": node_span(sm, statement),
        "signal": signal["name"],
        "edge": {
            EdgeKind.PosEdge: "posedge",
            EdgeKind.NegEdge: "negedge",
            EdgeKind.None_: "any",
        }[timing.edge],
    }
    body = convert_stmt(sm, statement.stmt)
    if body.get("kind") == "Empty":
        return wait
    return {
        "kind": "Block",
        "span": node_span(sm, statement),
        "stmts": [wait, body],
    }


def _case_source_expression_ok(expression):
    """Check bound source operands before constant folding can erase effects."""
    pure = True

    def check(node):
        nonlocal pure
        kind = type(node).__name__
        if kind == "CallExpression" and _fixed_bits_query_width(node) is not None:
            return VisitAction.Skip
        if kind == "CallExpression" and _bit_query_call(node):
            pure = pure and all(type_width_2s(argument.type)[0] is not None
                                for argument in node.arguments)
            return
        if kind == "CallExpression" and _signing_call(node):
            pure = pure and _signing_signature_ok(node)
            return
        pure = pure and not getattr(node, "bad", False) and kind in (
            "IntegerLiteral", "UnbasedUnsizedIntegerLiteral", "StringLiteral",
            "NamedValueExpression", "ConversionExpression", "UnaryExpression",
            "BinaryExpression", "ConditionalExpression", "ConcatenationExpression",
            "ElementSelectExpression", "RangeSelectExpression",
        )
        if kind == "UnaryExpression":
            pure = pure and (node.op in UNARY_OPS or node.op in REDUCE_OPS)
        if kind == "BinaryExpression":
            pure = pure and node.op in BINARY_OPS

    expression.visit(check)
    return pure


def _case_expression_ok(node):
    """Case comparisons may repeat only admitted, pure integral expressions."""
    if isinstance(node, dict):
        return node.get("kind") != "Unsupported" and all(
            _case_expression_ok(value) for value in node.values()
        )
    if isinstance(node, list):
        return all(_case_expression_ok(value) for value in node)
    return True


def _convert_ordinary_case(sm, stmt):
    """Lower pure IEEE 12.5 ordinary cases using bound whole-case sizing."""
    if stmt.check != UniquePriorityCheck.None_:
        return unsupported(sm, stmt, "CaseStatement:" + str(stmt.check).split(".")[-1])
    if str(stmt.condition).split(".")[-1] != "Normal":
        return unsupported(sm, stmt, "CaseStatement:" + str(stmt.condition).split(".")[-1])
    if not _case_source_expression_ok(stmt.expr):
        return unsupported(sm, stmt, "CaseStatement:subject")
    subject = convert_expr(sm, stmt.expr)
    width, _, _ = type_width_2s(stmt.expr.type)
    if width is None or width_of(subject) != width or not _case_expression_ok(subject):
        return unsupported(sm, stmt, "CaseStatement:subject")
    branches = []
    for item in stmt.items:
        body = convert_stmt(sm, item.stmt)
        for expression in item.expressions:
            if not _case_source_expression_ok(expression):
                return unsupported(sm, stmt, "CaseStatement:pattern")
            pattern = convert_expr(sm, expression)
            pattern_width, _, _ = type_width_2s(expression.type)
            if (pattern_width != width or width_of(pattern) != width
                    or not _case_expression_ok(pattern)):
                return unsupported(sm, stmt, "CaseStatement:pattern")
            branches.append((pattern, body))
    if not branches:
        return unsupported(sm, stmt, "CaseStatement:empty")
    result = convert_stmt(sm, stmt.defaultCase) if stmt.defaultCase is not None else None
    span = node_span(sm, stmt)
    for pattern, body in reversed(branches):
        result = {
            "kind": "If", "span": span, "case_lowered": True,
            "cond": {"kind": "Binary", "span": span, "width": 1,
                     "op": "===", "left": subject, "right": pattern},
            "then": body, "else": result,
        }
    return result


def _convert_for_step(sm, expression):
    if type(expression).__name__ == "AssignmentExpression":
        return _convert_assignment_expr(sm, expression)
    return _convert_incdec(sm, expression, "ForLoopStatement:step")


def _convert_incdec(sm, expression, context):
    op = str(getattr(expression, "op", None)).split(".")[-1]
    if type(expression).__name__ != "UnaryExpression" or op not in (
            "Preincrement", "Postincrement", "Predecrement", "Postdecrement"):
        return unsupported(sm, expression, context)
    target, ok = ident_target(sm, expression.operand)
    if not ok:
        return unsupported(sm, expression, context + "-target")
    width, two_state, reason = type_width_2s(expression.operand.type)
    if width is None or reason is not None:
        return unsupported(sm, expression, context + "-type")
    value = {
        "kind": "Binary", "span": node_span(sm, expression), "width": width,
        "op": "+" if op.endswith("increment") else "-", "left": target,
        "right": {"kind": "Literal", "span": None, "width": width,
                  "bits": "0" * (width - 1) + "1"},
    }
    if two_state:
        value = squash2_wrap(value, width)
    return {"kind": "BlockingAssign", "span": node_span(sm, expression),
            "target": target, "value": value}


def contains_local_decl(node):
    if isinstance(node, dict):
        return node.get("kind") == "LocalDecl" or any(
            contains_local_decl(value) for value in node.values())
    if isinstance(node, list):
        return any(contains_local_decl(value) for value in node)
    return False


def _convert_assignment_expr(sm, expr, span_node=None):
    if type(expr).__name__ != "AssignmentExpression":
        return unsupported(sm, span_node or expr,
                           "AssignmentExpression:" + type(expr).__name__)
    if expr.timingControl is not None:
        return unsupported(sm, span_node or expr, "AssignmentExpression:timing")
    if expr.op is None and _SYM is None:
        array_assignment = _fixed_array_pattern_assignment(sm, expr)
        if array_assignment is not None:
            return array_assignment
    if expr.op is not None:
        if _SYM is not None:
            return unsupported(sm, span_node or expr, "AssignmentExpression:compound")
        target, ok = ident_target(sm, expr.left)
        sym = BINARY_OPS.get(expr.op)
        if not ok or sym is None:
            return unsupported(sm, span_node or expr, "AssignmentExpression:compound")
        left = target
        rhs = _compound_rhs(expr.right)
        right = convert_expr(sm, rhs)
        width = getattr(expr.type, "bitWidth", None)
        if width is None or not _binary_width_ok(sym, width,
                                                 width_of(left), width_of(right)):
            return unsupported(sm, span_node or expr, "AssignmentExpression:compound-width")
        if sym == "/":
            sym = "s/" if expr.left.type.isSigned and rhs.type.isSigned else "u/"
        if sym == "%":
            sym = "s%" if expr.left.type.isSigned and rhs.type.isSigned else "u%"
        if sym in ("<<", ">>", "<<<", ">>>"):
            sym = ("s" if expr.left.type.isSigned else "u") + sym
        value = {
            "kind": "Binary",
            "span": node_span(sm, expr),
            "width": width,
            "op": sym,
            "left": left,
            "right": right,
        }
    else:
        if _SYM is None:
            target, ok = legacy_blocking_target(sm, expr.left)
        else:
            target, ok = select_target(sm, expr.left)
        if not ok:
            return unsupported(sm, span_node or expr, "AssignmentExpression:target")
        if (target.get("kind") in ("SelectTarget", "ConcatTarget")
                and not _case_source_expression_ok(expr.right)):
            return unsupported(sm, span_node or expr, "AssignmentExpression:selected-effects")
        value = convert_expr(sm, expr.right)
    try:
        if not expr.left.type.isFourState:
            value = squash2_wrap(value, expr.left.type.bitWidth)
    except Exception:
        pass
    return {
        "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
        "span": node_span(sm, span_node or expr),
        "target": target,
        "value": value,
    }


def _convert_expression_stmt(sm, stmt):
    expr = stmt.expr
    if type(expr).__name__ == "CallExpression":
        return _convert_syscall(sm, stmt, expr)
    if type(expr).__name__ == "UnaryExpression":
        op = str(getattr(expr, "op", None)).split(".")[-1]
        if op in ("Preincrement", "Postincrement", "Predecrement", "Postdecrement"):
            return _convert_incdec(sm, expr, "ExpressionStatement:UnaryExpression")
    if type(expr).__name__ != "AssignmentExpression":
        return unsupported(sm, stmt, "ExpressionStatement:" + type(expr).__name__)
    return _convert_assignment_expr(sm, expr, stmt)


def _convert_local_decl(sm, stmt):
    symbol = stmt.symbol
    width, two_state, reason = type_width_2s(symbol.type)
    if width is None:
        if reason == "type" and not getattr(symbol.type, "isFourState", True):
            reason = "2state"
        return unsupported(sm, stmt, "VariableDeclStatement:" + reason)
    initializer = getattr(symbol, "initializer", None)
    init_node = convert_expr(sm, initializer) if initializer is not None else None
    if two_state and init_node is not None:
        init_node = squash2_wrap(init_node, width)
    return signed_metadata({
        "kind": "LocalDecl",
        "span": node_span(sm, stmt),
        "name": symbol.name,
        "width": width,
        "two_state": two_state,
        "init": init_node,
    }, symbol.type)


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
    if (_SYM is None
            and type(getattr(m, "internalSymbol", None)).__name__ == "VariableSymbol"):
        w, two, reason = type_width_2s(m.type)
    else:
        w, reason = type_width(m.type)
        two = False
    if w is None:
        return unsupported(sm, m, "PortSymbol:" + reason)
    port = {
        "kind": "Port",
        "span": sym_span(sm, m),
        "name": m.name,
        "dir": direction,
        "width": w,
    }
    signed_metadata(port, m.type)
    if two:
        port["two_state"] = True
    initializer = getattr(m, "initializer", None)
    if initializer is None:
        initializer = getattr(getattr(m, "internalSymbol", None), "initializer", None)
        if initializer is not None and direction == "in":
            return unsupported(sm, m, "PortSymbol:input-variable-initializer")
    if initializer is not None:
        if (direction == "out"
                and type(getattr(m, "internalSymbol", None)).__name__ != "VariableSymbol"):
            return unsupported(sm, m, "PortSymbol:net-initializer")
        value = convert_expr(sm, initializer)
        port["init"] = squash2_wrap(value, w) if two else value
    return port


def convert_var(sm, m):
    array_decls = convert_fixed_array_vars(sm, m)
    if array_decls is not None:
        return array_decls
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
    return signed_metadata({
        "kind": "Var",
        "span": sym_span(sm, m),
        "name": m.name,
        "width": w,
        "init": init_d,
    }, m.type)


def convert_fixed_array_vars(sm, m):
    """Lower a narrow fixed-unpacked declaration to independent cells.

    This is the declaration half of `_fixed_array_cell`.  Only a single,
    constant-range unpacked dimension with an integral scalar/packed element
    and no aggregate initializer is admitted.  The existing vector state
    then gives each cell the ordinary 4-state/2-state initialization rules.
    """
    try:
        array_type = m.type.canonicalType
        if type(array_type).__name__ != "FixedSizeUnpackedArrayType":
            return None
        element_type = array_type.elementType
        if type(element_type.canonicalType).__name__ == "FixedSizeUnpackedArrayType":
            return None
        width, two, reason = type_width_2s(element_type)
        if width is None or reason is not None:
            return None
        left, right = int(array_type.range.left), int(array_type.range.right)
        count = abs(left - right) + 1
        # Avoid turning a malformed/hostile bound into an enormous envelope.
        if count > 1024:
            return None
        initializer = getattr(m, "initializer", None)
        values = [None] * count
        if initializer is not None:
            if type(initializer).__name__ != "SimpleAssignmentPatternExpression":
                return None
            elements = list(initializer.elements)
            if len(elements) != count:
                return None
            for i, element in enumerate(elements):
                value = convert_expr(sm, element)
                if value is None or value.get("kind") == "Unsupported":
                    return None
                values[i] = value
        step = 1 if right >= left else -1
        decls = []
        for i, position in enumerate(range(left, right + step, step)):
            init = values[i]
            if init is None and two:
                init = {
                    "kind": "Literal", "span": None, "width": width,
                    "bits": "0" * width,
                }
            elif init is not None and two:
                init = squash2_wrap(init, width)
            decls.append(signed_metadata({
                "kind": "Var",
                "span": sym_span(sm, m),
                "name": f"{m.name}[{position}]",
                "width": width,
                "init": init,
            }, element_type))
        return decls
    except Exception:
        return None


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
    return signed_metadata({
        "kind": "Net",
        "span": sym_span(sm, m),
        "name": m.name,
        "width": w,
        "init": convert_expr(sm, init) if init is not None else None,
    }, m.type)


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
                    converted = convert_var(sm, m)
                    if isinstance(converted, list):
                        decls.extend(converted)
                    else:
                        decls.append(converted)
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
            elif k == "TypeAlias" and is_integral_type_alias(m):
                continue
            elif is_bound_enum_member(m):
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


def contains_selected_read(node):
    if isinstance(node, dict):
        return node.get("kind") == "SelectRead" or any(
            contains_selected_read(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_selected_read(value) for value in node)
    return False


def contains_selected_target(node):
    if isinstance(node, dict):
        return node.get("kind") == "SelectTarget" or any(
            contains_selected_target(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_selected_target(value) for value in node)
    return False


def contains_concat_target(node):
    if isinstance(node, dict):
        return node.get("kind") == "ConcatTarget" or any(
            contains_concat_target(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_concat_target(value) for value in node)
    return False


def contains_lowered_case(node):
    if isinstance(node, dict):
        return node.get("case_lowered", False) or any(
            contains_lowered_case(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_lowered_case(value) for value in node)
    return False


def contains_fixed_bits_query(node):
    if isinstance(node, dict):
        return node.get("fixed_bits_query", False) or any(
            contains_fixed_bits_query(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_fixed_bits_query(value) for value in node)
    return False


def contains_fixed_clog2(node):
    if isinstance(node, dict):
        return node.get("fixed_clog2", False) or any(
            contains_fixed_clog2(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_fixed_clog2(value) for value in node)
    return False


def contains_fixed_dimension_query(node):
    if isinstance(node, dict):
        return node.get("fixed_dimension_query") in DIMENSION_QUERY_CALLS or any(
            contains_fixed_dimension_query(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_fixed_dimension_query(value) for value in node)
    return False


def contains_bit_vector_query(node):
    if isinstance(node, dict):
        return node.get("kind") == "BitQuery" or any(
            contains_bit_vector_query(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_bit_vector_query(value) for value in node)
    return False


def contains_signing_cast(node):
    if isinstance(node, dict):
        return bool(node.get("signing_cast")) or any(
            contains_signing_cast(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_signing_cast(value) for value in node)
    return False


def contains_multiplication(node):
    if isinstance(node, dict):
        return (node.get("kind") == "Binary" and node.get("op") == "*") or any(
            contains_multiplication(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_multiplication(value) for value in node)
    return False


def contains_division(node):
    if isinstance(node, dict):
        return (node.get("kind") == "Binary" and node.get("op") in ("/", "u/", "s/")) or any(
            contains_division(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_division(value) for value in node)
    return False


def contains_remainder(node):
    if isinstance(node, dict):
        return (node.get("kind") == "Binary" and node.get("op") in ("%", "u%", "s%")) or any(
            contains_remainder(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_remainder(value) for value in node)
    return False


def contains_power(node):
    if isinstance(node, dict):
        return (node.get("kind") == "Binary" and node.get("op") in ("**", "u**u", "u**s", "s**u", "s**s")) or any(
            contains_power(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_power(value) for value in node)
    return False


def contains_shift(node):
    if isinstance(node, dict):
        return (node.get("kind") == "Binary" and node.get("op") in (
            "<<", ">>", "<<<", ">>>", "u<<", "s<<", "u>>", "s>>",
            "u<<<", "s<<<", "u>>>", "s>>>")) or any(
            contains_shift(value) for value in node.values()
        )
    if isinstance(node, list):
        return any(contains_shift(value) for value in node)
    return False


def contains_loop(node):
    if isinstance(node, dict):
        return node.get("kind") in ("For", "Repeat", "Break", "Continue") or any(
            contains_loop(value) for value in node.values())
    if isinstance(node, list):
        return any(contains_loop(value) for value in node)
    return False


def convert_design(sm, comp):
    modules = []
    others = []
    for inst in comp.getRoot().topInstances:
        try:
            modules.append(convert_module(sm, inst))
        except Exception as exc:
            modules.append(internal_error(exc))
    # Runtime $unit-scope members (imports, unit variables, ...) are outside M0.
    try:
        for unit in comp.getCompilationUnits():
            for m in unit:
                if is_integral_type_alias(m) or is_bound_enum_member(m):
                    continue
                others.append(unsupported(sm, m, type(m).__name__))
    except Exception as exc:
        others.append(internal_error(exc))
    if (any(contains_selected_read(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "SelectRead:invalid-compilation",
                                  "frontend rejected source containing a selected read"))
    if (any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())
            and contains_bound_enum(comp)):
        others.append(unsupported(sm, comp, "Enum:invalid-compilation",
                                  "frontend rejected source containing an enumeration"))
    if (any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())
            and contains_admitted_type_alias(comp)):
        others.append(unsupported(sm, comp, "TypeAlias:invalid-compilation",
                                  "frontend rejected source containing an admitted type alias"))
    if (any(contains_lowered_case(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "CaseStatement:invalid-compilation",
                                  "frontend rejected source containing a lowered case"))
    if (any(contains_fixed_bits_query(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "$bits:invalid-compilation",
                                  "frontend rejected source containing a fixed-size query"))
    if (any(contains_fixed_clog2(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "$clog2:invalid-compilation",
                                  "frontend rejected source containing a constant clog2 call"))
    if (any(contains_fixed_dimension_query(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "DimensionQuery:invalid-compilation",
                                  "frontend rejected source containing a fixed dimension query"))
    if (any(contains_bit_vector_query(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "BitQuery:invalid-compilation",
                                  "frontend rejected source containing a bit-vector query"))
    if (any(contains_signing_cast(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "SigningCast:invalid-compilation",
                                  "frontend rejected source containing a signing cast"))
    if (any(contains_multiplication(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "Multiplication:invalid-compilation",
                                  "frontend rejected source containing multiplication"))
    if (any(contains_division(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "Division:invalid-compilation",
                                  "frontend rejected source containing division"))
    if (any(contains_remainder(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "Remainder:invalid-compilation",
                                  "frontend rejected source containing remainder"))
    if (any(contains_power(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "Power:invalid-compilation",
                                  "frontend rejected source containing power"))
    if (any(contains_shift(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "Shift:invalid-compilation",
                                  "frontend rejected source containing a shift"))
    if (any(contains_loop(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "Loop:invalid-compilation",
                                  "frontend rejected source containing a loop"))
    if (any(contains_selected_target(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "SelectTarget:invalid-compilation",
                                  "frontend rejected source containing a selected assignment"))
    if (any(contains_concat_target(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "ConcatTarget:invalid-compilation",
                                  "frontend rejected source containing a concatenated assignment"))
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
    if _DIV_CONTEXT and not _SYM.symctx and op.type.isIntegral and e.type.isIntegral:
        inner = _convert_expr(sm, op)
        if state_squash:
            inner = {"kind": "Squash2", "span": node_span(sm, e), "width": ow,
                     "operand": inner}
        return {"kind": "SignedResize" if op.type.isSigned and e.type.isSigned else "Resize",
                "span": node_span(sm, e), "width": tw, "operand": inner}
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
            if contains_division(module) and nerr:
                module["others"].append(unsupported(sm, comp, "Division:invalid-compilation",
                                                  "frontend rejected source containing division"))
            if contains_remainder(module) and nerr:
                module["others"].append(unsupported(sm, comp, "Remainder:invalid-compilation",
                                                  "frontend rejected source containing remainder"))
            if contains_power(module) and nerr:
                module["others"].append(unsupported(sm, comp, "Power:invalid-compilation",
                                                  "frontend rejected source containing power"))
            if contains_shift(module) and nerr:
                module["others"].append(unsupported(sm, comp, "Shift:invalid-compilation",
                                                  "frontend rejected source containing a shift"))
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
