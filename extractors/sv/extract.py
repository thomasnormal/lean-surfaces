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
    CompilationOptions,
    ConversionKind,
    EdgeKind,
    MinTypMax,
    LookupFlags,
    ProceduralBlockKind,
    Scope,
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
_COMPOUND_READ = None
_MIN_TYP_MAX = "typ"


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
        if cname == "EnumType":
            if _SYM is None:
                return type_width_2s(ct.baseType)
            return ct.bitWidth, (not t.isFourState), None
        if cname == "PackedArrayType":
            w = ct.bitWidth
            elem = ct.elementType.canonicalType
            # Packed dimensions form one contiguous integral vector.  Walk
            # through every packed layer before checking the scalar leaf for
            # two-state declarations; the LVec state already preserves the
            # complete bit ordering. Four-state multidimensional ranges keep
            # their existing explicit range boundary.
            if t.isFourState and type(elem).__name__ == "PackedArrayType":
                return None, None, "range"
            while type(elem).__name__ == "PackedArrayType":
                elem = elem.elementType.canonicalType
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


def is_flat_unpacked_struct_alias(symbol):
    """Whether a typedef names a shallow integral unpacked struct.

    Such a typedef is metadata for the legacy field-flattening path; it does
    not allocate an aggregate value by itself. Nested and nonintegral fields
    remain declaration boundaries until they have their own representation.
    """
    if str(symbol.kind) != "SymbolKind.TypeAlias":
        return False
    try:
        aggregate = symbol.declaredType.type.canonicalType
        if type(aggregate).__name__ != "UnpackedStructType":
            return False
        if getattr(aggregate, "isTagged", False):
            return False
        fields = list(aggregate)
        if not fields:
            return False
        for field in fields:
            width, _, reason = type_width_2s(field.type)
            if width is None or reason is not None:
                return False
            if type(field.type.canonicalType).__name__ in (
                    "FixedSizeUnpackedArrayType", "DynamicArrayType",
                    "QueueType", "AssociativeArrayType", "UnpackedStructType",
                    "UnpackedUnionType"):
                return False
        return True
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
    if (_contains_guarded_expression(e, guard_calls=_SYM is None)
            or _contains_disputed_string_escape(e)
            or _contains_unsized_based_widening(e)):
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


def _visit_selected_expression(expression, inspect):
    """Expression analyses visit only the elaboration-selected MTM arm."""
    def visit(node):
        action = inspect(node)
        if (_SYM is None and type(node).__name__ == "MinTypMaxExpression"
                and action != VisitAction.Skip):
            _visit_selected_expression(node.selected, inspect)
            return VisitAction.Skip
        return action
    expression.visit(visit)


def _contains_guarded_expression(expression, *, guard_calls):
    """Keep call/membership admission and provenance through conversions."""
    found = False

    def inspect(node):
        nonlocal found
        if _SYM is None and type(node).__name__ == "MinTypMaxExpression":
            found = True
            return VisitAction.Skip  # Preserve selection provenance through folds.
        if guard_calls and _unresolved_clog2(node):
            found = True
            return VisitAction.Skip
        if (type(node).__name__ == "InsideExpression"
                or (type(node).__name__ == "BinaryExpression"
                    and node.op in (BinaryOperator.LogicalImplication,
                                    BinaryOperator.LogicalEquivalence))):
            found = True
            return VisitAction.Skip
        if _enum_method_call(node, include_name=True):
            found = True
            return VisitAction.Skip
        if (guard_calls and type(node).__name__ == "CallExpression" and node.isSystemCall
                and node.subroutineName in
                ("$bits", *BIT_QUERY_CALLS, *SIGNING_CALLS, *DIMENSION_QUERY_CALLS)):
            found = True
            return VisitAction.Skip

    _visit_selected_expression(expression, inspect)
    return found


def _bits_argument_source_ok(expression):
    """Effectful query operands remain outside the licensed-confirmed tier."""
    pure = True

    def inspect(node):
        nonlocal pure
        kind = type(node).__name__
        if (_SYM is None and kind == "HierarchicalValueExpression"
                and (node.symbol in _ELAB_HIER_VALUES or node.symbol in _ELAB_PARAMETERS)):
            return
        if _SYM is None and _clog2_call(node):
            pure = pure and len(node.arguments) == 1 and all(
                argument.type.isIntegral and _bits_argument_source_ok(argument)
                for argument in node.arguments)
            return VisitAction.Skip
        if kind == "CallExpression" and _fixed_bits_query_width(node) is not None:
            return VisitAction.Skip
        if kind == "CallExpression" and _signing_call(node):
            pure = pure and _signing_signature_ok(node)
            return
        pure = pure and not getattr(node, "bad", False) and kind in (
            "DataTypeExpression", "IntegerLiteral", "UnbasedUnsizedIntegerLiteral",
            "StringLiteral", "RealLiteral", "NamedValueExpression",
            "ConversionExpression", "UnaryExpression", "BinaryExpression",
            "ConditionalExpression", "ConcatenationExpression", "MinTypMaxExpression",
            "ReplicationExpression", "ElementSelectExpression",
            "RangeSelectExpression", "MemberAccessExpression",
        )
        if kind == "UnaryExpression":
            pure = pure and node.op not in (
                UnaryOperator.Preincrement, UnaryOperator.Predecrement,
                UnaryOperator.Postincrement, UnaryOperator.Postdecrement,
            )

    _visit_selected_expression(expression, inspect)
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
ENUM_NUMERIC_METHODS = ("first", "last", "next", "prev", "num")
DIMENSION_QUERY_CALLS = (
    "$size", "$high", "$left", "$right", "$low", "$increment",
    "$dimensions", "$unpacked_dimensions",
)


def _signing_call(expression):
    return (type(expression).__name__ == "CallExpression"
            and not expression.bad and expression.isSystemCall
            and expression.subroutineName in SIGNING_CALLS)


def _enum_method_call(expression, include_name=False):
    return (type(expression).__name__ == "CallExpression"
            and expression.isSystemCall
            and expression.subroutineName in (ENUM_NUMERIC_METHODS + (("name",) if include_name else ()))
            and len(expression.arguments) > 0
            and type(expression.arguments[0].type.canonicalType).__name__ == "EnumType")


def _enum_literal(sm, expression, sv_type, value):
    width, _, reason = type_width_2s(sv_type)
    if (reason is not None or type(value).__name__ != "SVInt"
            or value.bitWidth != width):
        return unsupported(sm, expression, "EnumMethod:member-type")
    return signed_metadata({"kind": "Literal", "span": node_span(sm, expression),
                            "width": width, "bits": svint_bits(value)}, sv_type)


def _enum_nat_literal(sm, expression, width, value):
    return {"kind": "Literal", "span": node_span(sm, expression), "width": width,
            "bits": format(value % (1 << width), "0%db" % width)}


def _enum_lookup(sm, expression, width, subject, cases, default):
    result = default
    for key, value in reversed(cases):
        result = {"kind": "Ternary", "span": node_span(sm, expression), "width": width,
                  "cond": _one_bit_binary(sm, expression, "===", subject, key),
                  "then": value, "else": result}
    return result


def _convert_enum_method(sm, expression):
    """Pure §6.19.5 declaration-order traversal, using existing value operations."""
    if _SYM is not None or expression.bad or not _case_source_expression_ok(expression):
        return unsupported(sm, expression, "EnumMethod:source")
    arguments = list(expression.arguments)
    receiver = arguments[0]
    method = expression.subroutineName
    enum_type = receiver.type.canonicalType
    members = _enum_members(enum_type)
    width, _, reason = type_width_2s(receiver.type)
    expected = (32, True) if method == "num" else (width, bool(receiver.type.isSigned))
    if (reason is not None or not members
            or (expression.type.bitWidth, bool(expression.type.isSigned)) != expected
            or len(arguments) not in ((1, 2) if method in ("next", "prev") else (1,))):
        return unsupported(sm, expression, "EnumMethod:signature")
    subject = convert_expr(sm, receiver)
    values = [_enum_literal(sm, expression, receiver.type, member.value.value)
              for member in members]
    default = _enum_literal(sm, expression, receiver.type, enum_type.defaultValue.value)
    if not _case_expression_ok([subject, values, default]):
        return unsupported(sm, expression, "EnumMethod:operand")
    if method in ("first", "last", "num"):
        result = (_enum_nat_literal(sm, expression, 32, len(members)) if method == "num"
                  else dict(values[0 if method == "first" else -1]))
    else:
        result = _lower_enum_traversal(sm, expression, arguments, subject, values, default)
    result["enum_method_lowered"] = method
    return signed_metadata(result, expression.type)


def _lower_enum_traversal(sm, expression, arguments, subject, values, default):
    if len(arguments) == 1:
        step = _enum_nat_literal(sm, expression, 32, 1)
    else:
        argument = arguments[1]
        if (argument.type.bitWidth != 32 or argument.type.isSigned
                or argument.type.isFourState):
            return unsupported(sm, expression, "EnumMethod:step-type")
        step = convert_expr(sm, argument)
        if not _case_expression_ok(step):
            return unsupported(sm, expression, "EnumMethod:step")
    count = len(values)
    direction = -1 if expression.subroutineName == "prev" else 1
    if step.get("kind") == "Literal" and set(step["bits"]) <= {"0", "1"}:
        offset = int(step["bits"], 2) % count
        cases = [(value, values[(index + direction * offset) % count])
                 for index, value in enumerate(values)]
        return _enum_lookup(sm, expression, default["width"], subject, cases, default)
    index_width = max(32, count.bit_length())
    if index_width != 32:
        step = {"kind": "Resize", "span": node_span(sm, expression),
                "width": index_width, "operand": step}
    reduced = {"kind": "Binary", "span": node_span(sm, expression),
               "width": index_width, "op": "u%", "left": step,
               "right": _enum_nat_literal(sm, expression, index_width, count)}
    cases = []
    for index, value in enumerate(values):
        results = [(_enum_nat_literal(sm, expression, index_width, offset),
                    values[(index + direction * offset) % count]) for offset in range(count)]
        cases.append((value, _enum_lookup(sm, expression, default["width"], reduced, results, default)))
    return _enum_lookup(sm, expression, default["width"], subject, cases, default)


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
    """Preserve the operand width; fold only a fully known bound argument."""
    try:
        arguments = list(expression.arguments)
    except Exception:
        return unsupported(sm, expression, "CallExpression:$clog2:signature")
    if len(arguments) != 1:
        return unsupported(sm, expression, "CallExpression:$clog2:arity")
    argument = arguments[0]
    width, _, reason = type_width_2s(argument.type)
    if (reason is not None or width is None
            or expression.type.bitWidth != 32 or not expression.type.isSigned
            or not _case_source_expression_ok(argument)):
        return unsupported(sm, expression, "CallExpression:$clog2:argument")
    literal = const_literal(sm, expression) if not _unresolved_clog2(expression) else None
    if literal is not None:
        literal["signed"] = True
        literal["fixed_clog2"] = True
        return literal
    operand = convert_expr(sm, argument)
    if width_of(operand) != width or not _case_expression_ok(operand):
        return unsupported(sm, expression, "CallExpression:$clog2:argument")
    return {"kind": "Clog2", "span": node_span(sm, expression), "width": 32,
            "signed": True, "operand": operand, "runtime_clog2": True}


def _unresolved_clog2(expression):
    if _SYM is not None or not _clog2_call(expression):
        return False
    arguments = list(expression.arguments)
    return len(arguments) != 1 or _constant_dimension_selector(arguments[0]) is None


def _contains_unresolved_clog2(expression):
    found = False
    def inspect(node):
        nonlocal found
        if _fixed_bits_query_width(node) is not None:
            return VisitAction.Skip  # The argument is inspected for type only.
        found = found or _unresolved_clog2(node)
    _visit_selected_expression(expression, inspect)
    return found


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
    if (_contains_unsized_based_widening(expression)
            or _contains_unresolved_clog2(expression)):
        return None
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


_PACKAGE_BINDINGS = {}
_PACKAGE_SCOPES = set()
_ELAB_BINDINGS = {}
_ELAB_PARAMETERS = set()
_ELAB_HIER_VALUES = set()
_ELAB_CURRENT_SCOPE = ""
_ARRAY_REDUCTION_VALUES = {}


def _storage_name(symbol):
    """Use the original package declaration even through imports/reexports."""
    if _SYM is not None:
        return symbol.name
    return _ELAB_BINDINGS.get(symbol, _PACKAGE_BINDINGS.get(symbol, symbol.name))


def _scoped_temp(prefix, offset, suffix=""):
    scope = _ELAB_CURRENT_SCOPE + ":" if _ELAB_CURRENT_SCOPE else ""
    return f"{prefix}{scope}{offset}{suffix}"


def _array_storage_name(symbol):
    """One flat storage name per bound procedural array declaration.

    Anonymous scopes have identical lexical paths in the frontend. The
    declaration's source offset distinguishes those bindings too. Avoid the
    frontend's process-global buffer counter so repeated extraction is stable;
    the module audit refuses collisions across buffers or source identifiers.
    """
    if _SYM is None and symbol in _ELAB_BINDINGS:
        return _storage_name(symbol)
    if _SYM is None and symbol.parentScope.isProceduralContext:
        location = symbol.location
        return f"$local_array:{location.offset}:{symbol.name}"
    return _storage_name(symbol)


def _fixed_array_dimensions(array_type, max_cells=1024):
    """Return unpacked dimensions and the integral leaf type.

    The self-check state stores vectors under names, so a bounded fixed
    unpacked aggregate can be represented by one name per leaf.  Keep the
    bound deliberately small: this helper is only for finite declarations,
    never queues or dynamic arrays.
    """
    try:
        dimensions = []
        current = array_type.canonicalType
        total = 1
        while type(current).__name__ == "FixedSizeUnpackedArrayType":
            left, right = int(current.range.left), int(current.range.right)
            count = abs(left - right) + 1
            if count <= 0:
                return None
            total *= count
            if max_cells is not None and total > max_cells:
                return None
            dimensions.append((left, right))
            current = current.elementType.canonicalType
        if not dimensions:
            return None
        return dimensions, current
    except Exception:
        return None


def _fixed_array_selection_prefix(expression):
    """Return ``(flat-name, selected-leaf-type)`` for constant cells.

    Unlike `_fixed_array_leaf_select`, this helper also accepts a
    nonintegral leaf such as a shallow unpacked struct.  The caller is then
    responsible for lowering that leaf's protocol (for example, its direct
    integral members).
    """
    try:
        selectors = []
        current = expression
        while type(current).__name__ == "ElementSelectExpression":
            position = _constant_dimension_selector(current.selector)
            if position is None:
                return None
            selectors.append(position)
            current = current.value
        if not _storage_expression(current):
            return None
        if str(current.symbol.kind) not in ("SymbolKind.Variable", "SymbolKind.Net"):
            return None
        shape = _fixed_array_dimensions(current.type, max_cells=None)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        if len(selectors) != len(dimensions):
            return None
        positions = list(reversed(selectors))
        for position, (left, right) in zip(positions, dimensions):
            if position < min(left, right) or position > max(left, right):
                return None
        name = _array_storage_name(current.symbol)
        for position in positions:
            name += f"[{position}]"
        return name, leaf_type
    except Exception:
        return None


def _fixed_array_leaf_select(sm, expression):
    """Flatten a constant selection through any number of fixed dimensions."""
    try:
        selected = _fixed_array_selection_prefix(expression)
        if selected is None:
            return None
        name, leaf_type = selected
        width, two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None:
            return None
        return name, width, two_state
    except Exception:
        return None


def _fixed_array_oob_select(sm, expression):
    """Recognize a fully constant out-of-bounds fixed-array selection."""
    try:
        selectors = []
        current = expression
        while type(current).__name__ == "ElementSelectExpression":
            position = _constant_dimension_selector(current.selector)
            if position is None:
                return False
            selectors.append(position)
            current = current.value
        if not _storage_expression(current):
            return False
        if str(current.symbol.kind) not in ("SymbolKind.Variable", "SymbolKind.Net"):
            return False
        shape = _fixed_array_dimensions(current.type, max_cells=None)
        if shape is None:
            return False
        dimensions, leaf_type = shape
        if len(selectors) != len(dimensions):
            return False
        # Do not turn an unsupported leaf type into a no-op: its declaration
        # still needs the ordinary type boundary to fire.
        width, _two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None:
            return False
        return any(
            position < min(left, right) or position > max(left, right)
            for position, (left, right) in zip(reversed(selectors), dimensions))
    except Exception:
        return False


def _foreach_storage_name(symbol):
    """Bind an automatic iterator by its declaration, including anonymous scopes."""
    return _scoped_temp("$foreach:", symbol.location.offset, ":" + symbol.name)


def _storage_expression(expression):
    kind = type(expression).__name__
    return kind == "NamedValueExpression" or (
        _SYM is None and kind == "HierarchicalValueExpression"
        and expression.symbol in _ELAB_HIER_VALUES)


def _fixed_array_cell(sm, expression):
    """Return the lowered cell for a constant element of a bounded fixed
    unpacked integral array, including nested dimensions.

    The self-check state is a map of vector-valued signals, not a general
    unpacked-array store.  A constant array element can nevertheless be
    represented exactly by giving each leaf cell its own state name.  Dynamic
    indices, whole-array expressions, and aggregate initializers remain
    outside this deliberately narrow lowering and stay loud.
    """
    return _fixed_array_leaf_select(sm, expression)


def _unpacked_struct_member(sm, expression):
    """Return the flattened cell for a direct integral unpacked-struct field.

    The legacy state has no aggregate object slot, but a struct whose fields
    are scalar/packed integral values can be represented exactly by one slot
    per field.  Keep this helper deliberately shallow: nested aggregates,
    array fields, dynamic selections and whole-struct operations remain loud.
    """
    try:
        if type(expression).__name__ != "MemberAccessExpression":
            return None
        value = expression.value
        if _storage_expression(value):
            base_name = _storage_name(value.symbol)
            aggregate = value.type.canonicalType
        else:
            selected = _fixed_array_selection_prefix(value)
            if selected is None:
                return None
            base_name, leaf_type = selected
            aggregate = leaf_type.canonicalType
        if type(aggregate).__name__ != "UnpackedStructType":
            return None
        member = expression.member
        width, two_state, reason = type_width_2s(member.type)
        if width is None or reason is not None:
            return None
        leaf = member.type.canonicalType
        if type(leaf).__name__ in ("FixedSizeUnpackedArrayType",
                                    "DynamicArrayType", "QueueType",
                                    "AssociativeArrayType", "UnpackedStructType",
                                    "UnpackedUnionType"):
            return None
        return {
            "name": f"{base_name}.{member.name}",
            "width": width,
            "two_state": two_state,
        }
    except Exception:
        return None


def _unpacked_struct_decls(sm, symbol):
    """Flatten a top-level untagged unpacked struct with integral fields."""
    try:
        aggregate = symbol.type.canonicalType
        if type(aggregate).__name__ != "UnpackedStructType":
            return None
        if getattr(aggregate, "isTagged", False):
            return None
        fields = list(aggregate)
        if not fields:
            return None
        initializer = getattr(symbol, "initializer", None)

        # A shallow struct has no aggregate slot in the legacy state.  Keep
        # the initializer at the field boundary and lower each selected
        # value into the same scalar/vector cell used by field reads/writes.
        # Positional patterns follow declaration order; keyed patterns use
        # pyslang's elaborated member setters and may provide a default for
        # omitted fields.  Other aggregate forms remain loud.
        field_values = None
        if initializer is not None:
            pattern_kind = type(initializer).__name__
            if pattern_kind == "SimpleAssignmentPatternExpression":
                elements = list(initializer.elements)
                if len(elements) != len(fields):
                    return None
                field_values = list(zip(fields, elements))
            elif pattern_kind == "StructuredAssignmentPatternExpression":
                # pyslang elaborates complete keyed/default patterns into
                # context-sized ``elements`` in declaration order.  A
                # partial keyed pattern is represented as InvalidExpression
                # by the frontend and is intentionally left unsupported.
                elements = list(initializer.elements)
                if len(elements) != len(fields):
                    return None
                field_values = list(zip(fields, elements))
            else:
                return None

            if getattr(initializer, "bad", False):
                return None
            converted_values = []
            for field, value in field_values:
                if value is None:
                    converted_values.append((field, None))
                    continue
                if not _case_source_expression_ok(value, packed_members=True):
                    return None
                converted = convert_expr(sm, value)
                width, _two_state, reason = type_width_2s(field.type)
                if (converted.get("kind") == "Unsupported"
                        or width_of(converted) != width
                        or not _case_expression_ok(converted)):
                    return None
                # Keep the converted value on the field pair.  This also
                # makes x/z-to-zero conversion explicit for bit fields.
                converted_values.append((field, converted))
            field_values = converted_values
        decls = []
        for field in fields:
            width, two_state, reason = type_width_2s(field.type)
            if width is None or reason is not None:
                return None
            leaf = field.type.canonicalType
            if type(leaf).__name__ in ("FixedSizeUnpackedArrayType",
                                        "DynamicArrayType", "QueueType",
                                        "AssociativeArrayType", "UnpackedStructType",
                                        "UnpackedUnionType"):
                return None
            init = None
            if field_values is not None:
                converted = next(value for candidate, value in field_values
                                 if candidate is field)
                if converted is not None:
                    init = squash2_wrap(converted, width) if two_state else converted
            if init is None and two_state:
                init = {"kind": "Literal", "span": None, "width": width,
                        "bits": "0" * width}
            decls.append(signed_metadata({
                "kind": "Var", "span": sym_span(sm, symbol),
                "name": f"{_storage_name(symbol)}.{field.name}",
                "width": width, "init": init,
            }, field.type))
        return decls
    except Exception:
        return None


def _fixed_array_shape(source):
    """Return the lowered-cell shape for a one-dimensional fixed array."""
    try:
        if not _storage_expression(source):
            return None
        if str(source.symbol.kind) != "SymbolKind.Variable":
            return None
        array_type = source.type.canonicalType
        if type(array_type).__name__ != "FixedSizeUnpackedArrayType":
            return None
        element_type = array_type.elementType
        if type(element_type.canonicalType).__name__ == "FixedSizeUnpackedArrayType":
            return None
        width, two_state, reason = type_width_2s(element_type)
        if width is None or reason is not None:
            return None
        left, right = int(array_type.range.left), int(array_type.range.right)
        count = abs(left - right) + 1
        if count <= 0 or count > 1024:
            return None
        return _array_storage_name(source.symbol), width, two_state, left, right
    except Exception:
        return None


def _fixed_array_slice_shape(source):
    """Return cell shape and source-order positions for a constant simple slice."""
    try:
        if type(source).__name__ != "RangeSelectExpression":
            return None
        if str(source.selectionKind).split(".")[-1] != "Simple":
            return None
        shape = _fixed_array_shape(source.value)
        if shape is None:
            return None
        name, width, two_state, array_left, array_right = shape
        start = _constant_dimension_selector(source.left)
        stop = _constant_dimension_selector(source.right)
        if start is None or stop is None:
            return None
        lo, hi = min(array_left, array_right), max(array_left, array_right)
        if (start < lo or start > hi or stop < lo or stop > hi
                or abs(start - stop) + 1 <= 0):
            return None
        step = 1 if stop >= start else -1
        positions = list(range(start, stop + step, step))
        return name, width, two_state, positions
    except Exception:
        return None


def _fixed_array_assignment_shape(source):
    """Whole array or simple constant slice as ordered cell positions."""
    slice_shape = _fixed_array_slice_shape(source)
    if slice_shape is not None:
        return slice_shape
    shape = _fixed_array_shape(source)
    if shape is None:
        return None
    name, width, two_state, left, right = shape
    step = 1 if right >= left else -1
    return name, width, two_state, list(range(left, right + step, step))


def _fixed_array_compare_expr(sm, expression, operator):
    """Lower equality of equal-length cell-expanded arrays to cell comparisons."""
    try:
        if type(expression).__name__ != "BinaryExpression":
            return None
        left = _fixed_array_assignment_shape(expression.left)
        right = _fixed_array_assignment_shape(expression.right)
        if left is None or right is None:
            return None
        left_name, left_width, _left_two, left_positions = left
        right_name, right_width, _right_two, right_positions = right
        if (len(left_positions) != len(right_positions)
                or left_width != right_width or not left_positions):
            return None
        comparisons = []
        for left_position, right_position in zip(left_positions, right_positions):
            comparisons.append({
                "kind": "Binary",
                "span": node_span(sm, expression),
                "width": 1,
                "op": operator,
                "left": {"kind": "Ident", "span": node_span(sm, expression.left),
                         "width": left_width,
                         "name": f"{left_name}[{left_position}]"},
                "right": {"kind": "Ident", "span": node_span(sm, expression.right),
                          "width": right_width,
                          "name": f"{right_name}[{right_position}]"},
            })
        result = comparisons[0]
        join = "&&" if operator in ("==", "===") else "||"
        for comparison in comparisons[1:]:
            result = {
                "kind": "Binary",
                "span": node_span(sm, expression),
                "width": 1,
                "op": join,
                "left": result,
                "right": comparison,
            }
        return result
    except Exception:
        return None


def _fixed_array_dynamic_read(sm, expression):
    """Lower a dynamic read to a finite conditional over expanded cells."""
    try:
        if type(expression).__name__ != "ElementSelectExpression":
            return None
        shape = _fixed_array_shape(expression.value)
        if shape is None:
            return None
        name, width, _two_state, left, right = shape
        index = expression.selector
        if _constant_dimension_selector(index) is not None:
            return None
        index_width, _index_two, index_reason = type_width_2s(index.type)
        if (index_width is None or index_reason is not None
                or not _case_source_expression_ok(index)):
            return None
        converted_index = convert_expr(sm, index)
        if (converted_index is None or not _case_expression_ok(converted_index)
                or width_of(converted_index) != index_width):
            return None
        result = {
            "kind": "Literal",
            "span": node_span(sm, expression),
            "width": width,
            "bits": "x" * width,
        }
        step = 1 if right >= left else -1
        mask = (1 << index_width) - 1
        for position in reversed(list(range(left, right + step, step))):
            literal = {
                "kind": "Literal",
                "span": node_span(sm, index),
                "width": index_width,
                "bits": format(position & mask, f"0{index_width}b"),
            }
            result = {
                "kind": "Ternary",
                "span": node_span(sm, expression),
                "width": width,
                "cond": {
                    "kind": "Binary",
                    "span": node_span(sm, index),
                    "width": 1,
                    "op": "===",
                    "left": converted_index,
                    "right": literal,
                },
                "then": {
                    "kind": "Ident",
                    "span": node_span(sm, expression.value),
                    "width": width,
                    "name": f"{name}[{position}]",
                },
                "else": result,
            }
        return result
    except Exception:
        return None


def _fixed_array_dynamic_assignment(sm, expr):
    """Lower a dynamic write to mutually exclusive per-cell branches."""
    try:
        if type(expr).__name__ != "AssignmentExpression" or expr.op is not None:
            return None
        lhs = expr.left
        if type(lhs).__name__ != "ElementSelectExpression":
            return None
        shape = _fixed_array_shape(lhs.value)
        if shape is None:
            return None
        name, width, two_state, left, right = shape
        index = lhs.selector
        if _constant_dimension_selector(index) is not None:
            return None
        index_width, _index_two, index_reason = type_width_2s(index.type)
        if (index_width is None or index_reason is not None
                or not _case_source_expression_ok(index)
                or not _case_source_expression_ok(expr.right)):
            return None
        converted_index = convert_expr(sm, index)
        value = convert_expr(sm, expr.right)
        if (converted_index is None or value is None
                or not _case_expression_ok(converted_index)
                or not _case_expression_ok(value)
                or width_of(converted_index) != index_width
                or width_of(value) != width):
            return None
        if two_state:
            value = squash2_wrap(value, width)
        result = None
        step = 1 if right >= left else -1
        mask = (1 << index_width) - 1
        for position in reversed(list(range(left, right + step, step))):
            target = {
                "kind": "Ident",
                "span": node_span(sm, lhs),
                "width": width,
                "name": f"{name}[{position}]",
            }
            branch = {
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": target,
                "value": value,
            }
            literal = {
                "kind": "Literal",
                "span": node_span(sm, index),
                "width": index_width,
                "bits": format(position & mask, f"0{index_width}b"),
            }
            result = {
                "kind": "If",
                "span": node_span(sm, expr),
                "cond": {
                    "kind": "Binary",
                    "span": node_span(sm, index),
                    "width": 1,
                    "op": "===",
                    "left": converted_index,
                    "right": literal,
                },
                "then": branch,
                "else": result,
            }
        return result
    except Exception:
        return None


def _fixed_array_pattern_assignment(sm, expr):
    """Lower one exact assignment pattern to a fixed-array's cells.

    The self-check state has no aggregate store: declarations of a narrow
    one-dimensional fixed unpacked array are already expanded to names such
    as ``a[0]``.  A whole-array assignment can therefore use the same state
    by expanding an exact positional pattern into a block of per-cell
    assignments.  Keep the lowering deliberately strict.  Simple and
    elaborated structured patterns must have one pure integral element per
    cell; a replicated pattern must have a constant repetition count equal to
    the array length.  No element may read the destination array.  The last
    guard preserves the source-level rule that the complete RHS is evaluated
    before any destination cell is updated; without it, a later element could
    observe an earlier lowered write.
    """
    try:
        if type(expr).__name__ != "AssignmentExpression":
            return None
        if expr.op is not None or expr.timingControl is not None:
            return None
        lhs = expr.left
        if not _storage_expression(lhs):
            return None
        if str(lhs.symbol.kind) != "SymbolKind.Variable":
            return None
        lhs_type = lhs.type.canonicalType
        if type(lhs_type).__name__ != "FixedSizeUnpackedArrayType":
            return None
        element_type = lhs_type.elementType
        if type(element_type.canonicalType).__name__ == "FixedSizeUnpackedArrayType":
            return None
        if type(element_type.canonicalType).__name__ == "PackedUnionType":
            return None
        element_width, element_two, reason = type_width_2s(element_type)
        if element_width is None or reason is not None:
            return None
        pattern = expr.right
        pattern_kind = type(pattern).__name__
        if pattern_kind not in (
                "SimpleAssignmentPatternExpression",
                "StructuredAssignmentPatternExpression",
                "ReplicatedAssignmentPatternExpression"):
            return None
        left, right = int(lhs_type.range.left), int(lhs_type.range.right)
        count = abs(left - right) + 1
        if count > 1024:
            return None
        if getattr(pattern, "bad", False):
            return None
        if pattern_kind == "ReplicatedAssignmentPatternExpression":
            # Slang keeps the repetition count as a bound constant.  A
            # nonconstant count would need a runtime aggregate shape, which
            # this cell-expanded state does not represent.
            repetition = getattr(getattr(pattern, "count", None),
                                 "constant", None)
            try:
                if hasattr(repetition, "value"):
                    repetition = repetition.value
                repetition = int(repetition)
            except (TypeError, ValueError, OverflowError):
                return None
            if repetition != count or repetition <= 0:
                if repetition <= 0:
                    return None
            source_elements = _pattern_source_elements(pattern)
            if not source_elements or repetition * len(source_elements) != count:
                return None
            elements = source_elements * repetition
        else:
            elements = _pattern_source_elements(pattern)
            if len(elements) != count:
                return None
        target_name = _array_storage_name(lhs.symbol)
        converted = []
        for element in elements:
            if not _case_source_expression_ok(element, packed_members=True):
                return None
            # A pure read of the destination would see a different value
            # after the first lowered cell write.  Reject that aliasing shape
            # instead of silently changing aggregate-assignment semantics.
            reads_target = False
            def inspect(node):
                nonlocal reads_target
                if type(node).__name__ in ("NamedValueExpression", "HierarchicalValueExpression"):
                    try:
                        reads_target = reads_target or _array_storage_name(node.symbol) == target_name
                    except Exception:
                        reads_target = True
            _visit_selected_expression(element, inspect)
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


def _fixed_array_concat_assignment(sm, expr):
    """Lower an exact unpacked-array concatenation into cell assignments."""
    try:
        if type(expr).__name__ != "AssignmentExpression" or expr.op is not None:
            return None
        lhs_shape = _fixed_array_assignment_shape(expr.left)
        if lhs_shape is None or type(expr.right).__name__ != "ConcatenationExpression":
            return None
        lhs_name, lhs_width, lhs_two, lhs_positions = lhs_shape
        values = []
        source_names = set()
        for operand in expr.right.operands:
            array_shape = _fixed_array_assignment_shape(operand)
            if array_shape is not None:
                source_name, source_width, _source_two, positions = array_shape
                if source_width != lhs_width:
                    return None
                source_names.add(source_name)
                for position in positions:
                    values.append({
                        "kind": "Ident", "span": node_span(sm, operand),
                        "width": source_width,
                        "name": f"{source_name}[{position}]",
                    })
                continue
            pattern_kind = type(operand).__name__
            if pattern_kind == "SimpleAssignmentPatternExpression":
                pattern_type = operand.type.canonicalType
                if type(pattern_type).__name__ != "FixedSizeUnpackedArrayType":
                    return None
                element_type = pattern_type.elementType
                pattern_width, _pattern_two, pattern_reason = type_width_2s(element_type)
                if pattern_width is None or pattern_reason is not None:
                    return None
                elements = list(operand.elements)
                if not elements:
                    return None
                for element in elements:
                    if (not _case_source_expression_ok(element)
                            or not element.type.isIntegral):
                        return None
                    value = convert_expr(sm, element)
                    if (value is None or value.get("kind") == "Unsupported"
                            or width_of(value) != pattern_width
                            or pattern_width != lhs_width
                            or not _case_expression_ok(value)):
                        return None
                    values.append(value)
                continue
            cell = _fixed_array_cell(sm, operand)
            if cell is not None:
                cell_name, cell_width, _cell_two = cell
                if cell_width != lhs_width:
                    return None
                source_names.add(cell_name.split("[", 1)[0])
                values.append({"kind": "Ident", "span": node_span(sm, operand),
                               "width": cell_width, "name": cell_name})
                continue
            if not _case_source_expression_ok(operand):
                return None
            value = convert_expr(sm, operand)
            if (value is None or value.get("kind") == "Unsupported"
                    or width_of(value) != lhs_width
                    or not _case_expression_ok(value)):
                return None
            values.append(value)
        if source_names and lhs_name in source_names:
            return None
        if len(values) != len(lhs_positions):
            return None
        stmts = []
        for position, value in zip(lhs_positions, values):
            if lhs_two:
                value = squash2_wrap(value, lhs_width)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                           "width": lhs_width,
                           "name": f"{lhs_name}[{position}]"},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts}
    except Exception:
        return None


def _fixed_array_initializer_values(sm, initializer, target_name, width, count):
    """Flatten one finite unpacked-array declaration initializer.

    Assignment patterns and unpacked concatenations both describe a sequence
    of leaf values.  The legacy state stores those leaves as independent
    cells, so an initializer is admitted only when every source item has a
    fixed, integral shape and the resulting sequence has exactly the target
    length.  Array operands are expanded in their declared index order; all
    scalar/pattern elements must be pure and width-exact.  A source read of
    the destination is rejected because declaration initialization samples
    the complete RHS before publishing any cell.
    """
    try:
        if initializer is None:
            return [None] * count

        def scalar_value(element):
            if not _case_source_expression_ok(element, packed_members=True):
                return None
            reads_target = False

            def inspect(node):
                nonlocal reads_target
                if type(node).__name__ in ("NamedValueExpression",
                                           "HierarchicalValueExpression"):
                    try:
                        reads_target = (reads_target or
                                        _array_storage_name(node.symbol) == target_name)
                    except Exception:
                        reads_target = True

            _visit_selected_expression(element, inspect)
            if reads_target:
                return None
            value = convert_expr(sm, element)
            if (value is None or value.get("kind") == "Unsupported"
                    or width_of(value) != width
                    or not _case_expression_ok(value)):
                return None
            return value

        def pattern_values(pattern):
            kind = type(pattern).__name__
            if kind not in ("SimpleAssignmentPatternExpression",
                            "StructuredAssignmentPatternExpression",
                            "ReplicatedAssignmentPatternExpression"):
                return None
            if getattr(pattern, "bad", False):
                return None
            pattern_type = pattern.type.canonicalType
            if type(pattern_type).__name__ != "FixedSizeUnpackedArrayType":
                return None
            element_type = pattern_type.elementType
            pattern_width, _pattern_two, pattern_reason = type_width_2s(element_type)
            if pattern_width != width or pattern_reason is not None:
                return None
            if kind == "ReplicatedAssignmentPatternExpression":
                repetition = getattr(getattr(pattern, "count", None),
                                     "constant", None)
                try:
                    if hasattr(repetition, "value"):
                        repetition = repetition.value
                    repetition = int(repetition)
                except (TypeError, ValueError, OverflowError):
                    return None
                sources = _pattern_source_elements(pattern)
                if repetition <= 0 or len(sources) != 1:
                    return None
                elements = sources * repetition
            else:
                elements = _pattern_source_elements(pattern)
            values = []
            for element in elements:
                value = scalar_value(element)
                if value is None:
                    return None
                values.append(value)
            return values

        if type(initializer).__name__ == "ConcatenationExpression":
            values = []
            for operand in initializer.operands:
                array_shape = _fixed_array_assignment_shape(operand)
                if array_shape is not None:
                    source_name, source_width, _source_two, positions = array_shape
                    if source_width != width or source_name == target_name:
                        return None
                    # Procedural local arrays are represented as static cells
                    # in this runner.  Inline a source array only when its own
                    # declaration initializer is a complete pure constant;
                    # otherwise preserving the source read would require a
                    # runtime local-store operation that this surface does
                    # not have.
                    source_symbol = getattr(operand, "symbol", None)
                    source_values = _fixed_array_initializer_values(
                        sm, getattr(source_symbol, "initializer", None),
                        source_name, source_width, len(positions))
                    if (source_values is None
                            or any(value is None for value in source_values)):
                        return None
                    values.extend(source_values)
                    continue
                nested = pattern_values(operand)
                if nested is not None:
                    values.extend(nested)
                    continue
                value = scalar_value(operand)
                if value is None:
                    return None
                values.append(value)
            return values if len(values) == count else None

        values = pattern_values(initializer)
        return values if values is not None and len(values) == count else None
    except Exception:
        return None


def _fixed_array_pattern_lhs_assignment(sm, expr):
    """Lower a positional unpacked assignment-pattern LHS to scalar cells.

    A pattern such as ``U3'{a, b, c} = values`` is a source-level
    decomposition of one fixed unpacked array.  The self-check state already
    stores each array cell independently, so an exact, pure one-dimensional
    array RHS can be paired with direct scalar destinations.  Do not admit
    nested patterns, effectful destinations, duplicate targets, width
    conversions, or an RHS that aliases one of those destinations: the
    cellwise lowering must preserve the source rule that the whole RHS is
    sampled before any destination is written; ordinary integral width and
    four-state-to-two-state conversions remain explicit in the emitted value.
    """
    try:
        if type(expr).__name__ != "AssignmentExpression":
            return None
        if expr.op is not None or expr.timingControl is not None:
            return None
        pattern = expr.left
        if type(pattern).__name__ not in (
                "SimpleAssignmentPatternExpression",
                "StructuredAssignmentPatternExpression"):
            return None
        rhs_shape = _fixed_array_assignment_shape(expr.right)
        if rhs_shape is None or not _case_source_expression_ok(expr.right):
            return None
        source_name, source_width, _source_two, source_positions = rhs_shape
        elements = _pattern_source_elements(pattern)
        if not elements or len(elements) != len(source_positions):
            return None
        destinations = []
        names = set()
        for element in elements:
            if type(element).__name__ != "AssignmentExpression":
                return None
            if element.op is not None or element.timingControl is not None:
                return None
            element_rhs = element.right
            while type(element_rhs).__name__ == "ConversionExpression":
                element_rhs = getattr(element_rhs, "operand", None)
                if element_rhs is None:
                    return None
            if type(element_rhs).__name__ != "EmptyArgumentExpression":
                return None
            target, admitted = ident_target(sm, element.left)
            if not admitted or target.get("kind") != "Ident":
                return None
            width = width_of(target)
            if width is None:
                return None
            name = target.get("name")
            if not name or name in names:
                return None
            names.add(name)
            destinations.append((target, bool(element.left.type.isFourState)))
        if any(name == source_name or name.startswith(source_name + "[")
               for name in names):
            return None
        source_signed = False
        try:
            source_element_type = expr.right.type.canonicalType.elementType
            source_signed = bool(source_element_type.isSigned)
        except Exception:
            pass
        stmts = []
        for (target, target_four_state), position in zip(destinations, source_positions):
            value = {
                "kind": "Ident",
                "span": node_span(sm, expr.right),
                "width": source_width,
                "name": f"{source_name}[{position}]",
            }
            try:
                target_width = width_of(target)
                if source_width != target_width:
                    value = {
                        "kind": "SignedResize" if source_signed else "Resize",
                        "span": node_span(sm, expr),
                        "width": target_width,
                        "operand": value,
                    }
                if not target_four_state:
                    value = squash2_wrap(value, target_width)
            except Exception:
                pass
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": target,
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts}
    except Exception:
        return None


def _fixed_array_copy_assignment(sm, expr):
    """Lower a whole-array copy when both sides already have cell storage."""
    try:
        if type(expr).__name__ != "AssignmentExpression" or expr.op is not None:
            return None
        lhs = expr.left
        rhs = expr.right
        lhs_slice = _fixed_array_slice_shape(lhs)
        rhs_slice = _fixed_array_slice_shape(rhs)
        lhs_shape = (_fixed_array_shape(lhs) if lhs_slice is None else None)
        rhs_shape = (_fixed_array_shape(rhs) if rhs_slice is None else None)
        if lhs_slice is None and lhs_shape is None:
            return None
        if rhs_slice is None and rhs_shape is None:
            return None
        if lhs_slice is not None:
            lhs_name, lhs_width, lhs_two, lhs_positions = lhs_slice
        else:
            lhs_name, lhs_width, lhs_two, lhs_left, lhs_right = lhs_shape
            lhs_step = 1 if lhs_right >= lhs_left else -1
            lhs_positions = list(range(lhs_left, lhs_right + lhs_step, lhs_step))
        if rhs_slice is not None:
            rhs_name, rhs_width, _rhs_two, rhs_positions = rhs_slice
        else:
            rhs_name, rhs_width, _rhs_two, rhs_left, rhs_right = rhs_shape
            rhs_step = 1 if rhs_right >= rhs_left else -1
            rhs_positions = list(range(rhs_left, rhs_right + rhs_step, rhs_step))
        lhs_count = len(lhs_positions)
        rhs_count = len(rhs_positions)
        if lhs_count != rhs_count or lhs_width != rhs_width:
            return None
        if lhs_name == rhs_name:
            # Cell-by-cell lowering would expose an earlier destination write
            # to a later RHS cell.  Keep every overlapping self-copy loud
            # rather than inventing a temporary aggregate snapshot.
            return None
        if not _case_source_expression_ok(rhs):
            return None
        stmts = []
        for lhs_position, rhs_position in zip(lhs_positions, rhs_positions):
            value = {
                "kind": "Ident",
                "span": node_span(sm, rhs),
                "width": rhs_width,
                "name": f"{rhs_name}[{rhs_position}]",
            }
            if lhs_two:
                value = squash2_wrap(value, lhs_width)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {
                    "kind": "Ident",
                    "span": node_span(sm, lhs),
                    "width": lhs_width,
                    "name": f"{lhs_name}[{lhs_position}]",
                },
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts}
    except Exception:
        return None


def _fixed_array_conditional_assignment(sm, expr):
    """Lower a pure conditional whole-array assignment cell by cell."""
    try:
        if type(expr).__name__ != "AssignmentExpression" or expr.op is not None:
            return None
        lhs_shape = _fixed_array_assignment_shape(expr.left)
        if lhs_shape is None or type(expr.right).__name__ != "ConditionalExpression":
            return None
        cond_expr = expr.right
        if len(cond_expr.conditions) != 1 or cond_expr.conditions[0].pattern is not None:
            return None
        then_shape = _fixed_array_assignment_shape(cond_expr.left)
        else_shape = _fixed_array_assignment_shape(cond_expr.right)
        if then_shape is None or else_shape is None:
            return None
        lhs_name, lhs_width, lhs_two, lhs_positions = lhs_shape
        then_name, then_width, _then_two, then_positions = then_shape
        else_name, else_width, _else_two, else_positions = else_shape
        lhs_count = len(lhs_positions)
        if (lhs_count != len(then_positions)
                or lhs_count != len(else_positions)
                or lhs_width != then_width or lhs_width != else_width):
            return None
        if lhs_name in (then_name, else_name):
            return None
        source_cond = cond_expr.conditions[0].expr
        if not _case_source_expression_ok(source_cond):
            return None
        condition = convert_expr(sm, source_cond)
        if condition is None or not _case_expression_ok(condition):
            return None
        stmts = []
        for lhs_position, then_position, else_position in zip(
                lhs_positions, then_positions, else_positions):
            value = {
                "kind": "Ternary",
                "span": node_span(sm, expr.right),
                "width": lhs_width,
                "cond": condition,
                "then": {
                    "kind": "Ident",
                    "span": node_span(sm, cond_expr.left),
                    "width": then_width,
                    "name": f"{then_name}[{then_position}]",
                },
                "else": {
                    "kind": "Ident",
                    "span": node_span(sm, cond_expr.right),
                    "width": else_width,
                    "name": f"{else_name}[{else_position}]",
                },
            }
            if lhs_two:
                value = squash2_wrap(value, lhs_width)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {
                    "kind": "Ident",
                    "span": node_span(sm, expr.left),
                    "width": lhs_width,
                    "name": f"{lhs_name}[{lhs_position}]",
                },
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts}
    except Exception:
        return None


def _fixed_array_slice_pattern_assignment(sm, expr):
    """Lower an exact positional pattern to a simple constant array slice."""
    try:
        if type(expr).__name__ != "AssignmentExpression" or expr.op is not None:
            return None
        lhs = expr.left
        if type(lhs).__name__ != "RangeSelectExpression":
            return None
        selection = str(lhs.selectionKind).split(".")[-1]
        if selection != "Simple":
            return None
        shape = _fixed_array_shape(lhs.value)
        if shape is None:
            return None
        name, width, two_state, array_left, array_right = shape
        start = _constant_dimension_selector(lhs.left)
        stop = _constant_dimension_selector(lhs.right)
        if start is None or stop is None:
            return None
        lo, hi = min(array_left, array_right), max(array_left, array_right)
        if start < lo or start > hi or stop < lo or stop > hi:
            return None
        step = 1 if stop >= start else -1
        positions = list(range(start, stop + step, step))
        pattern = expr.right
        pattern_kind = type(pattern).__name__
        if pattern_kind not in (
                "SimpleAssignmentPatternExpression",
                "StructuredAssignmentPatternExpression",
                "ReplicatedAssignmentPatternExpression"):
            return None
        if getattr(pattern, "bad", False):
            return None
        if pattern_kind == "ReplicatedAssignmentPatternExpression":
            repetition = getattr(getattr(pattern, "count", None),
                                 "constant", None)
            try:
                if hasattr(repetition, "value"):
                    repetition = repetition.value
                repetition = int(repetition)
            except (TypeError, ValueError, OverflowError):
                return None
            if repetition != len(positions) or repetition <= 0:
                return None
            source_elements = _pattern_source_elements(pattern)
            if len(source_elements) != 1:
                return None
            elements = source_elements * repetition
        else:
            elements = _pattern_source_elements(pattern)
            if len(elements) != len(positions):
                return None
        values = []
        for element in elements:
            if not _case_source_expression_ok(element, packed_members=True):
                return None
            reads_target = False
            def inspect(node):
                nonlocal reads_target
                if type(node).__name__ in ("NamedValueExpression", "HierarchicalValueExpression"):
                    try:
                        reads_target = reads_target or _array_storage_name(node.symbol) == name
                    except Exception:
                        reads_target = True
            _visit_selected_expression(element, inspect)
            if reads_target:
                return None
            value = convert_expr(sm, element)
            if (value is None or value.get("kind") == "Unsupported"
                    or width_of(value) != width or not _case_expression_ok(value)):
                return None
            values.append(squash2_wrap(value, width) if two_state else value)
        stmts = []
        for position, value in zip(positions, values):
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {
                    "kind": "Ident",
                    "span": node_span(sm, lhs),
                    "width": width,
                    "name": f"{name}[{position}]",
                },
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts}
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


def _convert_selected_leaf(sm, expression, kind):
    """Resolve elaboration-selected leaves and a captured compound read."""
    if _SYM is not None:
        return None
    if kind == "MinTypMaxExpression":
        return _convert_min_typ_max(sm, expression)
    if kind == "LValueReferenceExpression" and _COMPOUND_READ is not None:
        if width_of(_COMPOUND_READ) == expression.type.bitWidth:
            return dict(_COMPOUND_READ)
        return unsupported(sm, expression, "AssignmentExpression:compound-read-width")
    return None


def _convert_expr(sm, e):
    if e is None:
        return None
    if getattr(e, "bad", False):
        return unsupported(sm, e, "InvalidExpression")

    cname = type(e).__name__
    selected = _convert_selected_leaf(sm, e, cname)
    if selected is not None:
        return selected
    if cname == "ConversionExpression":
        return _convert_conversion_expr(sm, e)
    if cname == "NamedValueExpression":
        return _convert_named_value_expr(sm, e)
    if (_SYM is None and cname == "HierarchicalValueExpression"
            and (e.symbol in _ELAB_HIER_VALUES or e.symbol in _ELAB_PARAMETERS)):
        node = _convert_named_value_expr(sm, e)
        node["elaboration_lowered"] = True
        return node
    if cname in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
        return _convert_integer_expr(sm, e, cname)
    if cname == "StringLiteral":
        return _convert_string_expr(sm, e)
    if cname == "UnaryExpression":
        return _convert_unary_expr(sm, e)
    if cname == "BinaryExpression":
        return _convert_binary_expr(sm, e)
    if cname == "InsideExpression" and _SYM is None:
        return _convert_inside_expr(sm, e)
    if cname == "ConditionalExpression":
        return _convert_conditional_expr(sm, e)
    if cname == "ConcatenationExpression":
        return _convert_concat_expr(sm, e)
    if _SYM is None and cname == "ReplicationExpression":
        return _convert_replication_expr(sm, e)
    if _SYM is None and cname in (
            "SimpleAssignmentPatternExpression", "StructuredAssignmentPatternExpression",
            "ReplicatedAssignmentPatternExpression"):
        return _convert_packed_pattern(sm, e)
    if cname == "MemberAccessExpression":
        unpacked_member = _unpacked_struct_member(sm, e)
        if unpacked_member is not None:
            return signed_metadata({
                "kind": "Ident",
                "span": node_span(sm, e),
                "width": unpacked_member["width"],
                "name": unpacked_member["name"],
            }, e.type)
        member = _packed_struct_member(sm, e)
        if member is not None:
            base, width, offset, _two_state = member
            if _SYM is not None:
                return {
                    "kind": "PartSel",
                    "span": node_span(sm, e),
                    "width": width,
                    "value": _convert_expr(sm, base),
                    "msb": {
                        "kind": "Int",
                        "span": node_span(sm, e),
                        "value": offset + width - 1,
                    },
                    "lsb": {
                        "kind": "Int",
                        "span": node_span(sm, e),
                        "value": offset,
                    },
                }

            return {
                "kind": "SelectRead",
                "span": node_span(sm, e),
                "width": width,
                "value": _convert_expr(sm, base),
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
        return _convert_legacy_call(sm, e) if _SYM is None else _convert_sym_call_expr(sm, e)
    if _SYM is not None and cname in (
        "ElementSelectExpression", "RangeSelectExpression", "ReplicationExpression"
    ):
        return _convert_sym_select_expr(sm, e, cname)
    return unsupported(sm, e)


def _convert_conversion_expr(sm, e):
    """Lower elaborated resizing after context signedness has propagated."""
    kind = e.conversionKind
    if kind == ConversionKind.StreamingConcat:
        return _convert_streaming_pack(sm, e)
    if kind == ConversionKind.Explicit:
        return _convert_integral_cast(sm, e)
    if kind not in (ConversionKind.Implicit, ConversionKind.Propagated):
        return unsupported(sm, e, "ConversionExpression:" + str(kind).split(".")[-1])
    corrected = _convert_unsized_based_widening(sm, e)
    if corrected is not None:
        return corrected
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


def _convert_streaming_pack(sm, expr):
    """IEEE 1800 §11.4.14: pure packed source streams, padded at right."""
    source = expr.operand
    token = getattr(getattr(expr, "syntax", None), "operatorToken", None)
    operator = str(getattr(token, "kind", "")).split(".")[-1]
    target_width, two_state, reason = type_width_2s(expr.type)
    if (type(source).__name__ != "StreamingConcatenationExpression"
            or operator not in ("RightShift", "LeftShift") or not source.isFixedSize
            or reason is not None or target_width is None or target_width <= 0):
        return unsupported(sm, expr, "ConversionExpression:StreamingConcat")
    # The padding below has a fixed width. Do not freeze a symbolic family's
    # defaults into it; parameter/generate-dependent streams need width terms.
    if _SYM is not None and (_SYM.scope is None or _SYM.genvars or any(
            type(member).__name__ in ("ParameterSymbol", "TypeParameterSymbol")
            and not getattr(member, "isLocalParam", False) for member in _SYM.scope)):
        return unsupported(sm, expr, "ConversionExpression:StreamingConcat")
    parts = []
    source_width = 0
    for stream in source.streams:
        operand = stream.operand
        width, _, reason = type_width_2s(operand.type)
        if (stream.withExpr is not None or reason is not None
                or width is None or width <= 0
                or not _case_source_expression_ok(operand)):
            return unsupported(sm, expr, "ConversionExpression:StreamingConcat")
        part = _convert_expr(sm, operand)
        if width_of(part) != width or not _case_expression_ok(part):
            return unsupported(sm, expr, "ConversionExpression:StreamingConcat")
        parts.append(part)
        source_width += width
    if (not parts or source_width != source.bitstreamWidth
            or source_width > target_width):
        return unsupported(sm, expr, "ConversionExpression:StreamingConcat")
    if operator == "LeftShift":
        if source.sliceSize <= 0:
            return unsupported(sm, expr, "ConversionExpression:StreamingConcat")
        parts = _streaming_left_parts(sm, expr, parts, source_width, source.sliceSize)
    if source_width < target_width:
        parts.append({
            "kind": "Literal", "span": node_span(sm, expr),
            "width": target_width - source_width,
            "bits": "0" * (target_width - source_width),
        })
    value = {
        "kind": "Concat", "span": node_span(sm, expr),
        "width": target_width, "parts": parts,
    }
    return squash2_wrap(value, target_width) if two_state else value


def _streaming_left_parts(sm, expr, parts, source_width, slice_size):
    """Emit low chunks first; the final high chunk keeps its actual width."""
    if slice_size >= source_width:
        return parts
    span = node_span(sm, expr)
    source = {"kind": "Concat", "span": span,
              "width": source_width, "parts": parts}
    chunks = []
    for offset in range(0, source_width, slice_size):
        width = min(slice_size, source_width - offset)
        if _SYM is not None:
            chunk = {
                "kind": "PartSel", "span": span, "width": width, "value": source,
                "msb": {"kind": "Int", "span": span, "value": offset + width - 1},
                "lsb": {"kind": "Int", "span": span, "value": offset},
            }
        else:
            index_width = max(32, offset.bit_length())
            chunk = {
                "kind": "SelectRead", "span": span, "width": width, "value": source,
                "index": {"kind": "Literal", "span": span, "width": index_width,
                          "bits": format(offset, "0%db" % index_width)},
                "index_signed": False, "descending": False,
            }
        chunks.append(chunk)
    return chunks


def _convert_integral_cast(sm, expr):
    """Integral casts resize using the operand's self-determined signedness.
    Nonintegral/exotic types and symbolic casts remain loud."""
    source_width, _, source_reason = type_width_2s(expr.operand.type)
    target_width, two_state, target_reason = type_width_2s(expr.type)
    if _SYM is not None or source_reason is not None or target_reason is not None:
        return unsupported(sm, expr, "ConversionExpression:Explicit")
    corrected = _convert_unsized_based_widening(sm, expr)
    if corrected is not None:
        return corrected
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


def _unsized_based_widening_bits(expression):
    """IEEE 5.7.1: an unsized based literal's leading X/Z fills its context.

    The frontend's bound conversion constant zero-extends this case. Only
    literal syntax is repaired here; ordinary unsigned values still zero-fill.
    """
    if _SYM is not None or type(expression).__name__ != "ConversionExpression":
        return None
    source = expression.operand
    if (type(source).__name__ != "IntegerLiteral" or not source.isDeclaredUnsized
            or not expression.type.isIntegral):
        return None
    target_width, _, reason = type_width_2s(expression.type)
    bits = svint_bits(source.value)
    if (reason is not None or target_width <= len(bits) or not bits
            or bits[0] not in "xz"):
        return None
    return bits[0] * (target_width - len(bits)) + bits


def _convert_min_typ_max(sm, expression):
    width, _, reason = type_width_2s(expression.type)
    selected = expression.selected
    if (reason is not None or width is None or width <= 0
            or not _case_source_expression_ok(selected, packed_members=True)):
        return unsupported(sm, expression, "MinTypMaxExpression:selected-source")
    value = convert_expr(sm, selected)
    if width_of(value) != width or not _case_expression_ok(value):
        return unsupported(sm, expression, "MinTypMaxExpression:selected-value")
    return signed_metadata({"kind": "MinTypMax", "span": node_span(sm, expression),
                            "width": width, "choice": _MIN_TYP_MAX, "value": value},
                           expression.type)


def _has_min_typ_max(comp):
    found = False
    def inspect(node):
        nonlocal found
        found = found or type(node).__name__ == "MinTypMaxExpression"
    comp.getRoot().visit(inspect)
    for unit in comp.getCompilationUnits():
        unit.visit(inspect)
    return found


def _contains_unsized_based_widening(expression):
    found = False
    def inspect(node):
        nonlocal found
        found = found or _unsized_based_widening_bits(node) is not None
    _visit_selected_expression(expression, inspect)
    return found


def _convert_unsized_based_widening(sm, expression):
    bits = _unsized_based_widening_bits(expression)
    if bits is None:
        return None
    if not expression.type.isFourState:
        bits = bits.replace("x", "0").replace("z", "0")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression), "width": len(bits),
        "bits": bits, "unsized_based_widening": True,
    }, expression.type)


def _constant_context_gap(comp, contains):
    """Inspect bound expressions before consuming elaboration constants."""
    found = False
    def inspect(node):
        nonlocal found
        kind = str(getattr(node, "kind", ""))
        if kind == "SymbolKind.TransparentMember":
            node = node.wrapped
            kind = str(node.kind)
        expressions = []
        if kind in ("SymbolKind.Parameter", "SymbolKind.EnumValue"):
            expressions = [node.initializer]
        elif kind == "SymbolKind.GenerateBlock":
            expressions = [node.conditionExpression, *node.caseItemExpressions]
        elif kind == "SymbolKind.GenerateBlockArray":
            expressions = [node.initialExpression, node.stopExpression, node.iterExpression]
        for expression in expressions:
            if expression is not None and contains(expression):
                found = True
    comp.getRoot().visit(inspect)
    for unit in comp.getCompilationUnits():
        unit.visit(inspect)
    return found


def _unsized_based_constant_gap(comp):
    """Do not consume a known incorrect parameter/enum/generate constant."""
    return _constant_context_gap(comp, _contains_unsized_based_widening)


def _convert_named_value_expr(sm, e):
    sym = e.symbol
    skind = str(sym.kind).split(".")[-1]
    if _SYM is None and sym in _ARRAY_REDUCTION_VALUES:
        return signed_metadata(dict(_ARRAY_REDUCTION_VALUES[sym]), e.type)
    if _SYM is not None:
        node = _sym_named_value(sm, e, sym, skind)
        if node is not None:
            return node
    if _SYM is None and skind == "EnumValue":
        return _convert_enum_member_expr(sm, e)
    if (_SYM is None and skind == "Parameter"
            and (sym in _PACKAGE_BINDINGS or sym in _ELAB_PARAMETERS)):
        node = _convert_enum_member_expr(sm, e, "Parameter")
        if sym in _ELAB_PARAMETERS:
            node["elaboration_lowered"] = True
        return node
    iterator = _SYM is None and skind == "Iterator"
    if skind not in ("Variable", "Net") and not iterator:
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
        "name": _foreach_storage_name(sym) if iterator else _storage_name(sym),
    }, e.type)


def _convert_enum_member_expr(sm, expr, kind="EnumValue"):
    """Preserve the exact, already-bound integral enumeration value."""
    width, _, reason = type_width_2s(expr.type)
    try:
        value = expr.symbol.value.value
        if (reason is not None or type(value).__name__ != "SVInt"
                or value.bitWidth != width):
            return unsupported(sm, expr, "NamedValueExpression:" + kind)
        return signed_metadata({
            "kind": "Literal",
            "span": node_span(sm, expr),
            "width": width,
            "bits": svint_bits(value),
        }, expr.type)
    except Exception:
        return unsupported(sm, expr, "NamedValueExpression:" + kind)


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


def _disputed_string_escape(expression):
    """Keep named control escapes loud while frontend/simulator disagree.

    Inspect token spelling, not decoded bytes: octal/hex controls and an
    escaped backslash followed by an ordinary a/v/f are distinct cases.
    """
    if type(expression).__name__ != "StringLiteral":
        return False
    syntax = getattr(expression, "syntax", None)
    if syntax is None:
        return any(char in expression.value for char in "\a\v\f")
    escaped = False
    for char in str(syntax):
        if escaped:
            if char in "avf":
                return True
            escaped = False
        elif char == "\\":
            escaped = True
    return False


def _contains_disputed_string_escape(expression):
    found = False

    def inspect(node):
        nonlocal found
        found = found or _disputed_string_escape(node)

    _visit_selected_expression(expression, inspect)
    return found


def _convert_string_expr(sm, e):
    if _disputed_string_escape(e):
        return unsupported(sm, e, "StringLiteral:named-control-escape")
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
    if e.op == BinaryOperator.LogicalImplication:
        return _convert_implication_expr(sm, e)
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
    if _SYM is None and sym in ("==", "!=", "===", "!=="):
        array_compare = _fixed_array_compare_expr(sm, e, sym)
        if array_compare is not None:
            return array_compare
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


def _one_bit_binary(sm, source, op, left, right):
    return {"kind": "Binary", "span": node_span(sm, source), "width": 1,
            "op": op, "left": left, "right": right}


def _convert_implication_expr(sm, expression):
    """Pure §11.4.7 implication, with self-determined integral operands."""
    if (expression.type.bitWidth != 1 or expression.type.isSigned
            or not expression.left.type.isIntegral
            or not expression.right.type.isIntegral
            or not _case_source_expression_ok(expression)):
        return unsupported(sm, expression, "BinaryExpression:LogicalImplication:source")
    left = _convert_expr(sm, expression.left)
    right = _convert_expr(sm, expression.right)
    if not _case_expression_ok([left, right]):
        return unsupported(sm, expression, "BinaryExpression:LogicalImplication:operand")
    if _DIV_CONTEXT and not _SYM.symctx:
        left = _division_self_operand(sm, expression.left, left)
        right = _division_self_operand(sm, expression.right, right)
    negated = {"kind": "Unary", "span": node_span(sm, expression),
               "width": 1, "op": "!", "operand": left}
    result = _one_bit_binary(sm, expression, "||", negated, right)
    result["implication_lowered"] = True
    return result


def _inside_scalar(sm, expression, width):
    actual_width, _, reason = type_width_2s(expression.type)
    if reason is not None or actual_width != width:
        return None
    value = convert_expr(sm, expression)
    if width_of(value) != width or not _case_expression_ok(value):
        return None
    return value


def _inside_bound(sm, expression, width, signed, upper, *, allow_unbounded=True):
    leaf = expression
    while type(leaf).__name__ == "ConversionExpression" and leaf.conversionKind in (
            ConversionKind.Implicit, ConversionKind.Propagated):
        leaf = leaf.operand
    if type(leaf).__name__ != "UnboundedLiteral":
        return _inside_scalar(sm, expression, width)
    if not allow_unbounded:
        return None
    # §11.4.13: dollar endpoints are the extrema of the propagated type.
    if signed:
        value = (1 << (width - 1)) - 1 if upper else 1 << (width - 1)
    else:
        value = (1 << width) - 1 if upper else 0
    return {"kind": "Literal", "span": node_span(sm, expression),
            "width": width, "bits": format(value, "0%db" % width)}


def _inside_item(sm, expression, subject, width, signed, *, allow_unbounded=True,
                 allow_array_widening=True):
    if type(expression).__name__ == "ValueRangeExpression":
        # Tolerance syntax shares this AST class; it is not a colon range.
        if str(expression.syntax.op.kind).split(".")[-1] != "Colon":
            return None
        lower = _inside_bound(sm, expression.left, width, signed, False,
                              allow_unbounded=allow_unbounded)
        upper = _inside_bound(sm, expression.right, width, signed, True,
                              allow_unbounded=allow_unbounded)
        if lower is None or upper is None:
            return None
        prefix = "s" if signed else ""
        return [_one_bit_binary(sm, expression, "&&",
            _one_bit_binary(sm, expression, prefix + ">=", subject, lower),
            _one_bit_binary(sm, expression, prefix + "<=", subject, upper))]
    shape = _fixed_array_assignment_shape(expression)
    if shape is not None:
        name, cell_width, _, positions = shape
        if cell_width > width or (not allow_array_widening and cell_width != width):
            return None
        values = []
        for position in positions:
            cell = {"kind": "Ident", "span": node_span(sm, expression),
                    "width": cell_width, "name": f"{name}[{position}]"}
            if cell_width != width:
                cell = {"kind": "SignedResize" if signed else "Resize",
                        "span": node_span(sm, expression), "width": width,
                        "operand": cell}
            values.append(cell)
    else:
        value = _inside_scalar(sm, expression, width)
        if value is None:
            return None
        values = [value]
    return [_one_bit_binary(sm, expression, "==?", subject, value)
            for value in values]


def _convert_inside_expr(sm, expression):
    """Pure integral §11.4.13 membership through existing scalar operators."""
    width, _, reason = type_width_2s(expression.left.type)
    if (reason is not None or width is None or width <= 0
            or expression.type.bitWidth != 1 or expression.type.isSigned
            or not _case_source_expression_ok(expression)):
        return unsupported(sm, expression, "InsideExpression:source")
    subject = _inside_scalar(sm, expression.left, width)
    if subject is None:
        return unsupported(sm, expression, "InsideExpression:subject")
    comparisons = []
    for item in expression.rangeList:
        converted = _inside_item(sm, item, subject, width, expression.left.type.isSigned)
        if not converted:
            return unsupported(sm, expression, "InsideExpression:item")
        comparisons.extend(converted)
    if not comparisons:
        return unsupported(sm, expression, "InsideExpression:empty")
    result = comparisons[0]
    for comparison in comparisons[1:]:
        result = _one_bit_binary(sm, expression, "||", result, comparison)
    result["inside_lowered"] = True
    return result


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


def _pattern_source_elements(pattern):
    """Map bound keyed inventories from numeric-index to declaration order.

    Positional and replicated patterns already retain source order. Struct
    inventories retain declaration order; keyed array / integer inventories
    enumerate increasing numeric indices, regardless of the declared range.
    """
    elements = list(pattern.elements)
    if type(pattern).__name__ == "StructuredAssignmentPatternExpression":
        shape = pattern.type.canonicalType
        kind = type(shape).__name__
        descending = kind == "PredefinedIntegerType" or (
            kind in ("PackedArrayType", "FixedSizeUnpackedArrayType")
            and int(shape.range.left) > int(shape.range.right))
        if descending:
            elements.reverse()
    return elements


def _fixed_array_pattern_elements(pattern, dimensions):
    """Flatten an exact assignment pattern over fixed unpacked dimensions.

    The legacy state has one vector slot per fixed-array leaf, so a nested
    pattern is admissible only when its complete finite shape is known at
    extraction time.  Replication is expanded at each dimension (including
    nested replication); positional patterns retain the declared dimension
    order, with ``_pattern_source_elements`` applying the descending-range
    rule.  The returned list is in the same order as the flattened storage
    names produced by ``convert_fixed_array_vars``.
    """
    if not dimensions:
        # At the leaf a pattern element must be one scalar/packed value.  A
        # composite pattern is consumed by the enclosing unpacked dimension.
        if type(pattern).__name__ in (
                "SimpleAssignmentPatternExpression",
                "StructuredAssignmentPatternExpression",
                "ReplicatedAssignmentPatternExpression"):
            return None
        return [pattern]
    if getattr(pattern, "bad", False):
        return None
    left, right = dimensions[0]
    count = abs(left - right) + 1
    tail_count = 1
    for tail_left, tail_right in dimensions[1:]:
        tail_count *= abs(tail_left - tail_right) + 1
    kind = type(pattern).__name__
    if kind == "ReplicatedAssignmentPatternExpression":
        repetition = getattr(getattr(pattern, "count", None), "constant", None)
        try:
            if hasattr(repetition, "value"):
                repetition = repetition.value
            repetition = int(repetition)
        except (TypeError, ValueError, OverflowError):
            return None
        if repetition <= 0:
            return None
        sources = _pattern_source_elements(pattern)
        if not sources:
            return None
        flattened_sources = [
            _fixed_array_pattern_elements(source, dimensions[1:])
            for source in sources
        ]
        if any(flattened is None or len(flattened) != tail_count
               for flattened in flattened_sources):
            return None
        if repetition * len(sources) != count:
            return None
        group = [value for flattened in flattened_sources for value in flattened]
        return group * repetition
    if kind not in ("SimpleAssignmentPatternExpression",
                    "StructuredAssignmentPatternExpression"):
        return None
    sources = _pattern_source_elements(pattern)
    if len(sources) != count:
        return None
    result = []
    for source in sources:
        flattened = _fixed_array_pattern_elements(source, dimensions[1:])
        if flattened is None or len(flattened) != tail_count:
            return None
        result.extend(flattened)
    return result


def _expression_node_cost(node, limit):
    """Count materialized AST nodes with an early stop at the envelope bound."""
    if isinstance(node, dict):
        total, children = int("kind" in node), node.values()
    elif isinstance(node, list):
        total, children = 0, node
    else:
        return 0
    for child in children:
        total += _expression_node_cost(child, max(0, limit - total))
        if total > limit:
            return limit + 1
    return total


def _convert_replication_expr(sm, expression):
    """Replicate a pure self-determined group, including legal empty members."""
    count = _constant_dimension_selector(expression.count)
    if count is None or count < 0:
        return unsupported(sm, expression, "Replication:constant-count")
    if count > 1024:
        return unsupported(sm, expression, "Replication:copy-limit")
    group_width, _, reason = type_width_2s(expression.concat.type)
    width = expression.type.bitWidth
    if (reason is not None or group_width <= 0 or count * group_width != width
            or (count == 0 and type(expression.type.canonicalType).__name__ != "VoidType")
            or (count > 0 and type_width_2s(expression.type)[0] != width)):
        return unsupported(sm, expression, "Replication:integral-shape")
    if not _case_source_expression_ok(expression, packed_members=True):
        return unsupported(sm, expression, "Replication:effects")
    group = convert_expr(sm, expression.concat)
    # Even at count zero, unsupported/effectful source operands stay visible.
    if count == 0 and _contains_unresolved_clog2(expression.concat):
        return unsupported(sm, expression, "Replication:operand")
    if not _case_expression_ok(group) or width_of(group) != group_width:
        return unsupported(sm, expression, "Replication:operand")
    if count and _expression_node_cost(group, 16384 // count) > 16384 // count:
        return unsupported(sm, expression, "Replication:expansion-limit")
    return {
        "kind": "Concat", "span": node_span(sm, expression), "width": width,
        "parts": [group] * count, "replication_lowered": True,
        "replication_count": count,
    }


def _convert_packed_pattern(sm, expression):
    """Pack pure, elaborated integral patterns through the ordinary concat rule."""
    width, _, reason = type_width_2s(expression.type)
    shape = expression.type.canonicalType
    kind = type(shape).__name__
    if reason is not None or kind not in (
            "PredefinedIntegerType", "PackedArrayType", "PackedStructType"):
        return unsupported(sm, expression, "AssignmentPattern:integral-shape")
    if kind == "PackedStructType":
        expected = [member.type.bitWidth for member in shape
                    if str(member.kind) == "SymbolKind.Field"]
    elif kind == "PackedArrayType":
        count = abs(int(shape.range.left) - int(shape.range.right)) + 1
        if count > 1024:
            return unsupported(sm, expression, "AssignmentPattern:element-limit")
        expected = [shape.elementType.bitWidth] * count
    else:
        if width > 1024:
            return unsupported(sm, expression, "AssignmentPattern:element-limit")
        expected = [1] * width
    elements = _pattern_source_elements(expression)
    if type(expression).__name__ == "ReplicatedAssignmentPatternExpression":
        count = _constant_dimension_selector(expression.count)
        if count is None or count <= 0 or count * len(elements) > 1024:
            return unsupported(sm, expression, "AssignmentPattern:repetition")
        elements *= count
    if (not elements or len(elements) > 1024 or len(elements) != len(expected)
            or [element.type.bitWidth for element in elements] != expected
            or sum(expected) != width):
        return unsupported(sm, expression, "AssignmentPattern:correspondence")
    if not _case_source_expression_ok(expression, packed_members=True):
        return unsupported(sm, expression, "AssignmentPattern:effects")
    parts = [convert_expr(sm, element) for element in elements]
    if (not _case_expression_ok(parts)
            or [width_of(part) for part in parts] != expected):
        return unsupported(sm, expression, "AssignmentPattern:element")
    return signed_metadata({
        "kind": "Concat", "span": node_span(sm, expression), "width": width,
        "parts": parts, "assignment_pattern_lowered": True,
        "source_pattern": type(expression).__name__,
    }, expression.type)


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


def _packed_element_index(sm, source_type, index):
    """Normalize a pure signed-int packed label without wrapping into valid bits.

    Foreach iterators have this type. Widen before subtracting the signed
    declaration bound; unknown/out-of-range offsets use selectedRead.
    Other index types retain the prior boundary: wide unsigned indices on
    negative ranges have an unresolved independent-observation discrepancy.
    """
    constant = _packed_constant_index(sm, source_type, index)
    if constant is not None or _constant_dimension_selector(index) is not None:
        return constant
    width, _, reason = type_width_2s(index.type)
    if (reason is not None or width != 32 or not index.type.isSigned
            or not _case_source_expression_ok(index)):
        return None
    value = _convert_expr(sm, index)
    if not _case_expression_ok(value):
        return None
    ct = source_type.canonicalType
    wide = width + 2
    value = {"kind": "SignedResize",
             "span": node_span(sm, index), "width": wide, "operand": value}
    right = {"kind": "Literal", "span": node_span(sm, index), "width": wide,
             "bits": format(int(ct.range.right) & ((1 << wide) - 1), f"0{wide}b")}
    left, right = (value, right) if ct.range.left > ct.range.right else (right, value)
    return {"kind": "Binary", "span": node_span(sm, index), "width": wide,
            "op": "-", "left": left, "right": right}, True


def _packed_constant_simple_index(sm, source_type, left, right, width):
    """Normalize a constant simple part-select's right label to an offset."""
    try:
        ct = source_type.canonicalType
        if type(ct).__name__ != "PackedArrayType":
            return None
        left_position = _constant_dimension_selector(left)
        right_position = _constant_dimension_selector(right)
        if left_position is None or right_position is None:
            return None
        declared_left, declared_right = int(ct.range.left), int(ct.range.right)
        lo, hi = min(declared_left, declared_right), max(declared_left, declared_right)
        if (left_position < lo or left_position > hi
                or right_position < lo or right_position > hi
                or abs(left_position - right_position) + 1 != int(width)):
            return None
        return _packed_constant_index(sm, source_type, right)
    except Exception:
        return None


def _packed_constant_indexed_index(sm, source_type, base, width, descending):
    """Normalize a constant indexed part-select base on any packed range."""
    try:
        ct = source_type.canonicalType
        if type(ct).__name__ != "PackedArrayType" or width <= 0:
            return None
        label = _constant_dimension_selector(base)
        if label is None:
            return None
        left, right = int(ct.range.left), int(ct.range.right)
        lo, hi = min(left, right), max(left, right)
        end = label - width + 1 if descending else label + width - 1
        if label < lo or label > hi or end < lo or end > hi:
            return None
        normalized = _packed_constant_index(sm, source_type, base)
        if normalized is None:
            return None
        literal, _ = normalized
        return literal, descending
    except Exception:
        return None


def _packed_struct_member(sm, expression):
    """Describe one direct integral field of a packed struct/union value."""
    try:
        if type(expression).__name__ != "MemberAccessExpression":
            return None
        value = expression.value
        if _storage_expression(value):
            base = value
            aggregate = base.type.canonicalType
            if type(aggregate).__name__ not in ("PackedStructType", "PackedUnionType"):
                return None
            if getattr(aggregate, "isTagged", False):
                return None
            parent_offset = 0
        elif type(value).__name__ == "ElementSelectExpression":
            # A constant cell of a fixed-unpacked array is already lowered to
            # one ordinary vector signal.  Reuse the same packed-member
            # offset on that cell; dynamic cells and nested-unpacked elements
            # fail the fixed-cell admission above.
            if _fixed_array_cell(sm, value) is None:
                return None
            base = value
            aggregate = value.type.canonicalType
            if type(aggregate).__name__ not in ("PackedStructType", "PackedUnionType"):
                return None
            if getattr(aggregate, "isTagged", False):
                return None
            parent_offset = 0
        elif type(value).__name__ == "MemberAccessExpression":
            parent = _packed_struct_member(sm, value)
            if parent is None:
                return None
            base, _parent_width, parent_offset, _parent_two = parent
            aggregate = value.type.canonicalType
            # Untagged packed structs and unions both have fixed declaration
            # offsets. A union's alternate members intentionally flatten to
            # overlapping windows on the same vector; the static continuous
            # driver guard rejects conflicting windows before they imply
            # resolution. Tagged aggregates remain outside this path.
            if type(aggregate).__name__ not in ("PackedStructType",
                                                  "PackedUnionType"):
                return None
        else:
            return None
        member = expression.member
        width, two_state, reason = type_width_2s(member.type)
        if width is None or reason is not None:
            return None
        offset = parent_offset + int(member.bitOffset)
        if offset < 0 or offset + width > base.type.canonicalType.bitWidth:
            return None
        return base, width, offset, two_state
    except Exception:
        return None


def _legacy_member_select_window(sm, expression, expression_kind, result_kind):
    """Flatten a constant selection inside a packed-member chain.

    Legacy selected reads/targets store one vector plus an LSB offset. A
    nested untagged packed-struct/union members have fixed outer offsets, so a
    constant bit or simple part select can add its local normalized offset and
    reuse that representation. Indexed, dynamic and tagged aggregate forms
    stay outside this helper rather than manufacturing a runtime aggregate
    path.
    """
    try:
        if type(expression.value).__name__ != "MemberAccessExpression":
            return None
        member = _packed_struct_member(sm, expression.value)
        if member is None:
            return None
        base, _member_width, parent_offset, _two_state = member
        normalized = None
        if expression_kind == "ElementSelectExpression":
            normalized = _packed_constant_index(
                sm, expression.value.type, expression.selector)
        elif expression_kind == "RangeSelectExpression":
            selection = str(expression.selectionKind).split(".")[-1]
            if selection == "Simple":
                normalized = _packed_constant_simple_index(
                    sm, expression.value.type, expression.left,
                    expression.right, expression.type.bitWidth)
            elif selection in ("IndexedUp", "IndexedDown"):
                normalized = _packed_constant_indexed_index(
                    sm, expression.value.type, expression.left,
                    expression.type.bitWidth, selection == "IndexedDown")
            else:
                return None
        if normalized is None:
            return None
        local_index, _index_signed = normalized
        bits = local_index.get("bits")
        if not isinstance(bits, str) or any(bit not in "01" for bit in bits):
            return None
        offset = parent_offset + int(bits, 2)
        index = {
            "kind": "Literal",
            "span": node_span(sm, expression),
            "width": 32,
            "bits": format(offset & ((1 << 32) - 1), "032b"),
        }
        result = {
            "kind": result_kind,
            "span": node_span(sm, expression),
            "width": expression.type.bitWidth,
            "value": _convert_expr(sm, base),
            "index": index,
            "index_signed": False,
            "descending": (normalized[1] if expression_kind ==
                            "RangeSelectExpression" and
                            str(expression.selectionKind).split(".")[-1]
                            in ("IndexedUp", "IndexedDown") else False),
        }
        if result_kind == "SelectTarget":
            result["two_state"] = not expression.type.isFourState
        return result
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
        dynamic_array = _fixed_array_dynamic_read(sm, expr)
        if dynamic_array is not None:
            return dynamic_array
    member_window = _legacy_member_select_window(
        sm, expr, expression_kind, "SelectRead")
    if member_window is not None:
        return member_window
    if (type(expr.value).__name__ == "MemberAccessExpression"
            and _packed_struct_member(sm, expr.value) is not None):
        return unsupported(sm, expr, expression_kind + ":member-select")
    source_type = expr.value.type
    _, source_two_state, source_reason = type_width_2s(source_type)
    canonical_kind = type(source_type.canonicalType).__name__
    canonical_select = _canonical_packed_select_source(source_type)
    if (source_reason is not None
            or canonical_kind not in ("PredefinedIntegerType", "PackedArrayType",
                                      "PackedStructType", "PackedUnionType")):
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
            and not canonical_select):
        normalized = _packed_element_index(sm, source_type, index)
        if normalized is None:
            return unsupported(sm, expr, expression_kind + ":source-type")
        converted_index, index_signed = normalized
    elif (expression_kind == "RangeSelectExpression"
          and canonical_kind == "PackedArrayType"
          and not canonical_select):
        selection = str(expr.selectionKind).split(".")[-1]
        if selection == "Simple":
            normalized = _packed_constant_simple_index(
                sm, source_type, expr.left, expr.right, expr.type.bitWidth)
        elif selection in ("IndexedUp", "IndexedDown"):
            normalized = _packed_constant_indexed_index(
                sm, source_type, expr.left, expr.type.bitWidth,
                selection == "IndexedDown")
        else:
            normalized = None
        if normalized is None:
            return unsupported(sm, expr, expression_kind + ":source-type")
        converted_index, index_signed = normalized
    else:
        _, _, index_reason = type_width_2s(index.type)
        if index_reason is not None:
            return unsupported(sm, expr, expression_kind + ":index-type")
        converted_index = _convert_expr(sm, index)
    result = {
        "kind": "SelectRead",
        "span": node_span(sm, expr),
        "width": expr.type.bitWidth,
        "value": _convert_expr(sm, expr.value),
        "index": converted_index,
        "index_signed": index_signed,
        "descending": descending,
    }

    # IEEE 11.5.1: invalid positions have the selected source's state kind.
    # Squash the RESULT so x-fill becomes zero for a two-state source;
    # squashing only the source would leave the evaluator's x-fill intact.
    return squash2_wrap(result, expr.type.bitWidth) if source_two_state else result


def _convert_legacy_call(sm, expression):
    for recognizes, convert in (
            (_plusargs_call, _convert_plusargs_call),
            (_dynamic_cast_call, _convert_dynamic_cast),
            (_array_reduction_call, _convert_array_reduction),
            (_enum_method_call, _convert_enum_method),
            (_clog2_call, _convert_clog2),
            (_dimension_query_call, _convert_dimension_query),
            (_time_call, _convert_time_call),
            (_signing_call, _convert_signing_call),
            (_bit_query_call, _convert_bit_query)):
        if recognizes(expression):
            return convert(sm, expression)
    return _convert_fixed_bits_query(sm, expression)


def _convert_sym_call_expr(sm, e):
    node = _sym_expr_syscall(sm, e)
    if node is not None:
        return node
    node = _sym_cast_call(sm, e)
    return node if node is not None else unsupported(sm, e)


def _convert_sym_select_expr(sm, e, cname):
    if cname == "ElementSelectExpression":
        cell = _fixed_array_cell(sm, e)
        if cell is not None:
            name, width, _two_state = cell
            return {
                "kind": "Ident",
                "span": node_span(sm, e),
                "width": width,
                "name": name,
            }
    member = None
    if (cname != "ReplicationExpression" and
            type(e.value).__name__ == "MemberAccessExpression"):
        member = _packed_struct_member(sm, e.value)
    if member is not None:
        base, _member_width, parent_offset, _two_state = member
        member_type = e.value.type.canonicalType
        if type(member_type).__name__ == "PackedArrayType":
            declared_left = int(member_type.range.left)
            declared_right = int(member_type.range.right)
            low, high = min(declared_left, declared_right), max(declared_left, declared_right)

            def offset(label):
                return (label - declared_right if declared_left > declared_right
                        else declared_right - label)

            if cname == "ElementSelectExpression":
                label = _constant_dimension_selector(e.selector)
                if (label is None or type(e.selector).__name__ not in
                        ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral") or
                        label < low or label > high):
                    return unsupported(sm, e, "ElementSelectExpression:member-index")
                bit = parent_offset + offset(label)
                return {
                    "kind": "PartSel",
                    "span": node_span(sm, e),
                    "width": 1,
                    "value": _convert_expr(sm, base),
                    "msb": {"kind": "Int", "span": node_span(sm, e),
                            "value": bit},
                    "lsb": {"kind": "Int", "span": node_span(sm, e),
                            "value": bit},
                }
            if cname == "RangeSelectExpression":
                selection = str(e.selectionKind).split(".")[-1]
                if selection in ("IndexedUp", "IndexedDown"):
                    base_label = _constant_dimension_selector(e.left)
                    width = _safe_width(e)
                    canonical = (declared_left == int(member_type.bitWidth) - 1
                                 and declared_right == 0)
                    if (not canonical or base_label is None or
                            type(e.left).__name__ not in
                            ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral") or
                            width <= 0):
                        return unsupported(sm, e,
                                           "RangeSelectExpression:member-indexed")
                    if selection == "IndexedUp":
                        msb_local, lsb_local = base_label + width - 1, base_label
                    else:
                        msb_local, lsb_local = base_label, base_label - width + 1
                    if (lsb_local < 0 or msb_local >= int(member_type.bitWidth)):
                        return unsupported(sm, e,
                                           "RangeSelectExpression:member-range")
                    return {
                        "kind": "PartSel",
                        "span": node_span(sm, e),
                        "width": width,
                        "value": _convert_expr(sm, base),
                        "msb": {"kind": "Int", "span": node_span(sm, e),
                                "value": parent_offset + msb_local},
                        "lsb": {"kind": "Int", "span": node_span(sm, e),
                                "value": parent_offset + lsb_local},
                    }
                left = _constant_dimension_selector(e.left)
                right = _constant_dimension_selector(e.right)
                if (selection != "Simple" or left is None or right is None
                        or type(e.left).__name__ not in
                        ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral")
                        or type(e.right).__name__ not in
                        ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral")
                        or left < low or left > high or right < low or right > high):
                    return unsupported(sm, e, "RangeSelectExpression:member-range")
                msb = parent_offset + offset(left)
                lsb = parent_offset + offset(right)
                if msb < lsb:
                    return unsupported(sm, e, "RangeSelectExpression:member-direction")
                return {
                    "kind": "PartSel",
                    "span": node_span(sm, e),
                    "width": _safe_width(e),
                    "value": _convert_expr(sm, base),
                    "msb": {"kind": "Int", "span": node_span(sm, e),
                            "value": msb},
                    "lsb": {"kind": "Int", "span": node_span(sm, e),
                            "value": lsb},
                }
    if cname == "ElementSelectExpression":
        index = e.selector
        source_type = e.value.type.canonicalType
        if type(source_type).__name__ == "PackedArrayType":
            left = int(source_type.range.left)
            right = int(source_type.range.right)
            position = _constant_dimension_selector(index)
            # Indices count outer elements. The semantic elaborator applies
            # their stride, so a multidimensional [N-1:0] range is canonical
            # even when its total bit width exceeds N.
            canonical = left >= 0 and right == 0
            if not canonical and position is not None and type(index).__name__ in (
                    "IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
                low, high = min(left, right), max(left, right)
                if position < low or position > high:
                    return unsupported(sm, e, "ElementSelectExpression:range")
                offset = position - right if left > right else right - position
                index = {"kind": "Int", "span": node_span(sm, e),
                         "value": offset}
            elif not canonical:
                return unsupported(sm, e, "ElementSelectExpression:dynamic-range")
        with _SymPos():
            if not isinstance(index, dict):
                index = _convert_expr(sm, index)
        return {
            "kind": "BitSel",
            "span": node_span(sm, e),
            "width": _safe_width(e),
            "value": _convert_expr(sm, e.value),
            "index": index,
        }
    if cname == "RangeSelectExpression":
        selection = str(e.selectionKind).split(".")[-1]
        if selection == "Simple":
            source_type = e.value.type.canonicalType
            source_kind = type(source_type).__name__
            left_value = _constant_dimension_selector(e.left)
            right_value = _constant_dimension_selector(e.right)
            # Canonical bounds remain expressions with their original spans.
            # A select outside the default width can be valid at another
            # parameter point, so only shifted/reversed labels are folded.
            if (source_kind == "PackedArrayType" and
                    not (int(source_type.range.left) >= 0 and
                         int(source_type.range.right) == 0) and
                    left_value is not None and right_value is not None and
                    type(e.left).__name__ in
                    ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral") and
                    type(e.right).__name__ in
                    ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral")):
                declared_left = int(source_type.range.left)
                declared_right = int(source_type.range.right)
                low = min(declared_left, declared_right)
                high = max(declared_left, declared_right)
                if (left_value < low or left_value > high or
                        right_value < low or right_value > high):
                    return unsupported(sm, e, "RangeSelectExpression:range")
                if declared_left > declared_right:
                    left_offset = left_value - declared_right
                    right_offset = right_value - declared_right
                else:
                    left_offset = declared_right - left_value
                    right_offset = declared_right - right_value
                if left_offset < right_offset:
                    return unsupported(sm, e, "RangeSelectExpression:direction")
                msb = {"kind": "Int", "span": node_span(sm, e),
                       "value": left_offset}
                lsb = {"kind": "Int", "span": node_span(sm, e),
                       "value": right_offset}
                return {
                    "kind": "PartSel",
                    "span": node_span(sm, e),
                    "width": _safe_width(e),
                    "value": _convert_expr(sm, e.value),
                    "msb": msb,
                    "lsb": lsb,
                }
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
        if selection not in ("IndexedUp", "IndexedDown"):
            return unsupported(sm, e, "RangeSelectExpression:" + selection)
        # A literal indexed base and fixed width can be normalized to the
        # existing constant PartSel executor. Parameter/dynamic bases stay
        # loud because folding them here would erase a family point.
        base = _constant_dimension_selector(e.left)
        width = _safe_width(e)
        if (base is None or type(e.left).__name__ not in
                ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral")
                or width <= 0):
            return unsupported(sm, e, "RangeSelectExpression:dynamic-indexed")
        if selection == "IndexedUp":
            msb_value, lsb_value = base + width - 1, base
        else:
            msb_value, lsb_value = base, base - width + 1
        source_type = e.value.type.canonicalType
        if type(source_type).__name__ == "PackedArrayType":
            left, right = int(source_type.range.left), int(source_type.range.right)
            low, high = min(left, right), max(left, right)
            if (lsb_value < low or msb_value > high or
                    msb_value < low or lsb_value > high):
                return unsupported(sm, e, "RangeSelectExpression:range")
        msb = {"kind": "Int", "span": node_span(sm, e),
               "value": msb_value}
        lsb = {"kind": "Int", "span": node_span(sm, e),
               "value": lsb_value}
        return {
            "kind": "PartSel",
            "span": node_span(sm, e),
            "width": width,
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
    if expression_kind in ("ElementSelectExpression", "RangeSelectExpression"):
        member_window = _legacy_member_select_window(
            sm, lhs, expression_kind, "SelectTarget")
        if member_window is not None:
            return member_window, True
        if (type(lhs.value).__name__ == "MemberAccessExpression"
                and _packed_struct_member(sm, lhs.value) is not None):
            return unsupported(sm, lhs, expression_kind + ":member-select"), False
    if expression_kind == "MemberAccessExpression":
        unpacked_member = _unpacked_struct_member(sm, lhs)
        if unpacked_member is not None:
            target = {
                "kind": "Ident",
                "span": node_span(sm, lhs),
                "width": unpacked_member["width"],
                "name": unpacked_member["name"],
            }
            if concat_leaf:
                target["two_state"] = unpacked_member["two_state"]
            return target, True
        member = _packed_struct_member(sm, lhs)
        if member is not None:
            _base, width, offset, two_state = member
            target = {
                "kind": "SelectTarget",
                "span": node_span(sm, lhs),
                "width": width,
                "value": convert_expr(sm, _base),
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
    canonical_select = _canonical_packed_select_source(lhs.value.type)
    if (not admitted or source_reason is not None or source_width is None
            or canonical_kind not in ("PredefinedIntegerType", "PackedArrayType")):
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
            and not canonical_select):
        normalized = _packed_constant_index(sm, lhs.value.type, index)
        if normalized is None:
            return unsupported(sm, lhs, expression_kind + ":target-source"), False
        converted_index, index_signed = normalized
    elif (expression_kind == "RangeSelectExpression"
          and canonical_kind == "PackedArrayType"
          and not canonical_select):
        selection = str(lhs.selectionKind).split(".")[-1]
        if selection == "Simple":
            normalized = _packed_constant_simple_index(
                sm, lhs.value.type, lhs.left, lhs.right, lhs.type.bitWidth)
        elif selection in ("IndexedUp", "IndexedDown"):
            normalized = _packed_constant_indexed_index(
                sm, lhs.value.type, lhs.left, lhs.type.bitWidth,
                selection == "IndexedDown")
        else:
            normalized = None
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


def _streaming_has_slice_size(lhs):
    """Return whether a streaming concatenation spells an explicit slice.

    Pyslang keeps the syntax node on ``lhs.syntax.sliceSize``; the elaborated
    expression's ``sliceSize`` property is zero for both the default and an
    explicit size.  Sized streams stay outside the fixed-window lowering.
    """
    try:
        syntax = getattr(lhs, "syntax", None)
        return syntax is None or getattr(syntax, "sliceSize", None) is not None
    except Exception:
        return True


def _streaming_source_window(value, width, symbolic):
    """Unpack the leading bits of a wider source (IEEE 1800 §11.4.14.3)."""
    source_width = width_of(value)
    if source_width == width:
        return value
    offset = source_width - width
    span = value.get("span")
    if symbolic:
        return {
            "kind": "PartSel", "span": span, "width": width, "value": value,
            "msb": {"kind": "Int", "span": span, "value": source_width - 1},
            "lsb": {"kind": "Int", "span": span, "value": offset},
        }
    index_width = max(32, offset.bit_length())
    return {
        "kind": "SelectRead", "span": span, "width": width, "value": value,
        "index": {"kind": "Literal", "span": span, "width": index_width,
                  "bits": format(offset, "0%db" % index_width)},
        "index_signed": False, "descending": False,
    }


def _streaming_target_assignment(sm, expr):
    """Lower a simple right-streaming unpack into packed target leaves.

    With no slice size and only direct integral identifiers or fixed packed
    member windows, right streaming consumes the source from its MSB into the
    listed targets. Constant chains through untagged packed structs/unions
    reuse those same flat windows, including their alias overlap guard. The
    RHS is sampled once; an excess source contributes its leading bits to
    the target, reusing the existing scheduler and storage. Nested streams, left streaming and dynamic/effectful
    target leaves remain loud.
    """
    try:
        if type(expr).__name__ != "AssignmentExpression":
            return None
        if expr.op is not None or expr.timingControl is not None:
            return None
        lhs = expr.left
        if type(lhs).__name__ != "StreamingConcatenationExpression":
            return None
        if _streaming_has_slice_size(lhs):
            return None
        token = getattr(getattr(lhs, "syntax", None), "operatorToken", None)
        operator = str(getattr(token, "kind", "")).split(".")[-1]
        if operator != "RightShift":
            return None
        parts = []
        total_width = 0
        for stream in lhs.streams:
            operand = getattr(stream, "operand", None)
            if operand is None:
                return None
            target, admitted = legacy_blocking_target(sm, operand, True)
            if not admitted or target.get("kind") not in ("Ident", "SelectTarget"):
                return None
            if target.get("kind") == "Ident":
                target_type = operand.type.canonicalType
                if type(target_type).__name__ not in (
                        "ScalarType", "PredefinedIntegerType",
                        "PackedArrayType", "EnumType", "PackedStructType",
                        "PackedUnionType"):
                    return None
            width = width_of(target)
            if width is None or width <= 0:
                return None
            parts.append(target)
            total_width += width
        if not parts:
            return None
        value = convert_expr(sm, expr.right)
        if (value is None or value.get("kind") == "Unsupported"
                or not _case_source_expression_ok(expr.right)
                or width_of(value) is None or width_of(value) < total_width
                or not _case_expression_ok(value)):
            return None
        value = _streaming_source_window(value, total_width, False)
        target = {
            "kind": "ConcatTarget",
            "span": node_span(sm, lhs),
            "width": total_width,
            "parts": parts,
        }
        windows = _symbolic_target_windows(target)
        if windows is None or any(
                old_base == base and not (high < old_low or old_high < low)
                for i, (base, low, high) in enumerate(windows)
                for old_base, old_low, old_high in windows[:i]):
            return None
        return {
            "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
            "span": node_span(sm, expr),
            "target": target,
            "value": value,
        }
    except Exception:
        return None


def _symbolic_streaming_target_assignment(sm, expr):
    """Lower a simple blocking right-streaming target in symbolic mode.

    The semantic tier already represents a sampled unpack as a ``ConcatTarget``
    and its comb executor splits that value across fixed windows.  Reuse that
    representation for constant packed selections and flattened fixed-array
    cells.  Dynamic/effectful leaves, left streaming, and sized/nested streams
    remain outside this storage-only rung.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None or expr.isNonBlocking):
            return None
        lhs = expr.left
        if type(lhs).__name__ != "StreamingConcatenationExpression":
            return None
        if _streaming_has_slice_size(lhs):
            return None
        token = getattr(getattr(lhs, "syntax", None), "operatorToken", None)
        operator = str(getattr(token, "kind", "")).split(".")[-1]
        if operator != "RightShift":
            return None
        parts = []
        total_width = 0
        leaf_two_state = []
        for stream in lhs.streams:
            operand = getattr(stream, "operand", None)
            if operand is None:
                return None
            target, admitted = select_target(sm, operand)
            if not admitted or target is None:
                return None
            if target.get("kind") not in ("Ident", "BitSel", "PartSel"):
                return None
            if target.get("kind") != "Ident":
                base = target.get("value")
                if base is None or base.get("kind") != "Ident":
                    return None
                if target.get("kind") == "BitSel":
                    index = target.get("index")
                    if index is None or index.get("kind") != "Int":
                        return None
                else:
                    if (target.get("msb", {}).get("kind") != "Int"
                            or target.get("lsb", {}).get("kind") != "Int"):
                        return None
            width = width_of(target)
            if width is None or width <= 0:
                return None
            try:
                leaf_two_state.append(not operand.type.isFourState)
            except Exception:
                return None
            parts.append(target)
            total_width += width
        if not parts:
            return None
        value = convert_expr(sm, expr.right)
        if (value is None or value.get("kind") == "Unsupported"
                or not _case_source_expression_ok(expr.right)
                or width_of(value) is None or width_of(value) < total_width
                or not _case_expression_ok(value)):
            return None
        # A ConcatTarget writes one sampled vector, so it cannot represent
        # per-leaf 4-state-to-2-state conversion.  Homogeneous leaves are
        # exact; mixed leaves stay loud until the target representation grows
        # a per-window conversion marker.
        if any(leaf_two_state) and not all(leaf_two_state):
            return None
        value = _streaming_source_window(value, total_width, True)
        if all(leaf_two_state):
            value = squash2_wrap(value, total_width)
        target = {
            "kind": "ConcatTarget",
            "span": node_span(sm, lhs),
            "width": total_width,
            "parts": parts,
        }
        # A single streaming assignment still has one sampled vector, so
        # overlapping leaves cannot be represented without net resolution or
        # an aggregate alias model. Keep the symbolic path aligned with the
        # legacy streaming lowering and reject statically known overlap.
        windows = _symbolic_target_windows(target)
        if windows is None or any(
                old_base == base and not (high < old_low or old_high < low)
                for i, (base, low, high) in enumerate(windows)
                for old_base, old_low, old_high in windows[:i]):
            return None
        return {
            "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
            "span": node_span(sm, expr),
            "target": target,
            "value": value,
        }
    except Exception:
        return None


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

    if cname in ("WhileLoopStatement", "DoWhileLoopStatement"):
        return _convert_test_loop(sm, s, cname)

    if cname == "ImmediateAssertionStatement":
        return _convert_immediate_assertion(sm, s)

    if cname == "ForeverLoopStatement":
        if _SYM is not None:
            return unsupported(sm, s)
        body = convert_stmt(sm, s.body)
        if contains_local_decl(body):
            return unsupported(sm, s, "ForeverLoopStatement:body-lifetime")
        return {"kind": "Forever", "span": node_span(sm, s), "body": body}

    if cname == "ForeachLoopStatement":
        return _convert_foreach_loop(sm, s)

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


def _literal_delay_amount(sm, expression, node, category):
    """The common admitted integral delay inventory; units stay explicit/loud."""
    while _SYM is None and type(expression).__name__ == "MinTypMaxExpression":
        expression = expression.selected
    if type(expression).__name__ != "IntegerLiteral" or not expression.type.isIntegral:
        return unsupported(sm, node, category + ":expression")
    bits = svint_bits(expression.value)
    if not bits or any(bit not in "01" for bit in bits):
        return unsupported(sm, node, category + ":unknown")
    if expression.type.isSigned and bits[0] == "1":
        return unsupported(sm, node, category + ":negative")
    amount = int(bits, 2)
    if amount >= 1 << 64:
        return unsupported(sm, node, category + ":range")
    return amount


def _convert_delay_statement(sm, statement):
    amount = _literal_delay_amount(sm, statement.timing.expr, statement,
                                   "TimedStatement:DelayControl")
    if isinstance(amount, dict):
        return amount
    return {"kind": "Delay", "span": node_span(sm, statement),
            "amount": amount, "body": convert_stmt(sm, statement.stmt)}


def _convert_event_wait(sm, timing, node):
    if timing.edge not in (EdgeKind.PosEdge, EdgeKind.NegEdge, EdgeKind.None_):
        return unsupported(sm, node, "SignalEventControl:" + str(timing.edge).split(".")[-1])
    if timing.iffCondition is not None:
        return unsupported(sm, node, "SignalEventControl:iff")
    signal = convert_expr(sm, timing.expr)
    if signal.get("kind") != "Ident" or signal.get("width") != 1:
        return unsupported(sm, node, "SignalEventControl:clock")
    return {"kind": "WaitEvent", "span": node_span(sm, node),
            "signal": signal["name"],
            "edge": {EdgeKind.PosEdge: "posedge", EdgeKind.NegEdge: "negedge",
                     EdgeKind.None_: "any"}[timing.edge]}


def _convert_wait_event_statement(sm, statement):
    wait = _convert_event_wait(sm, statement.timing, statement)
    if wait.get("kind") == "Unsupported":
        return wait
    body = convert_stmt(sm, statement.stmt)
    if body.get("kind") == "Empty":
        return wait
    return {"kind": "Block", "span": node_span(sm, statement), "stmts": [wait, body]}


def _convert_intra_assignment(sm, expression):
    """IEEE 10.4.1/9.4.5: capture RHS, wait, then resolve the destination.

    Only the source compiler changes. Timer registration, zero-delay refusal,
    repeat sampling and residual execution use their existing core rules. A future NBA must never be implemented by a synthetic sleeper.
    """
    if _SYM is not None or expression.isNonBlocking or expression.op is not None:
        return unsupported(sm, expression, "IntraAssignment:publication-or-context")
    width, _, reason = type_width_2s(expression.left.type)
    if (reason is not None or width is None or width <= 0
            or not _case_source_expression_ok(expression.left)
            or not _case_source_expression_ok(expression.right)):
        return unsupported(sm, expression, "IntraAssignment:type-or-effects")
    target, admitted = legacy_blocking_target(sm, expression.left, True)
    value = convert_expr(sm, expression.right)
    if not admitted or not _case_expression_ok([target, value]) or width_of(value) != width:
        return unsupported(sm, expression, "IntraAssignment:packed-target-or-value")
    timing = expression.timingControl
    kind = type(timing).__name__
    span = node_span(sm, expression)
    if kind == "DelayControl":
        amount = _literal_delay_amount(sm, timing.expr, expression, "IntraAssignment:delay")
        if isinstance(amount, dict):
            return amount
        wait = {"kind": "Delay", "span": span, "amount": amount,
                "body": {"kind": "Empty", "span": None}}
    elif kind == "SignalEventControl":
        wait = _convert_event_wait(sm, timing, expression)
    elif kind == "RepeatedEventControl" and type(timing.event).__name__ == "SignalEventControl":
        count_width, _, count_reason = type_width_2s(timing.expr.type)
        if count_width is None or count_reason is not None or not _case_source_expression_ok(timing.expr):
            return unsupported(sm, expression, "IntraAssignment:repeat-count")
        wait = {"kind": "Repeat", "span": span, "count": convert_expr(sm, timing.expr),
                "count_signed": bool(timing.expr.type.isSigned),
                "body": _convert_event_wait(sm, timing.event, expression)}
    else:
        return unsupported(sm, expression, "IntraAssignment:timing-control")
    if not _case_expression_ok(wait):
        return wait
    name = _scoped_temp("$intra:", expression.sourceRange.start.offset)
    captured = {"kind": "Ident", "span": None, "name": name, "width": width}
    capture = {"kind": "LocalDecl", "span": span, "name": name, "width": width,
               "two_state": False, "init": value, "automatic_intra": True}
    # A singleton packed target retains width/state conversion for whole and
    # selected destinations alike. Selectors execute only after the wait.
    copyback = {"kind": "BlockingAssign", "span": span,
                "target": {"kind": "ConcatTarget", "span": span, "width": width,
                           "parts": [target]}, "value": captured}
    return {"kind": "Block", "span": span, "stmts": [capture, wait, copyback],
            "intra_assignment_lowered": True}


def _array_reduction_call(expression):
    return (type(expression).__name__ == "CallExpression" and expression.isSystemCall
            and expression.subroutineName in ("sum", "product", "and", "or", "xor"))


def _array_reduction_source_ok(expression):
    if (expression.bad or len(expression.arguments) != 1
            or _fixed_array_shape(expression.arguments[0]) is None):
        return False
    info = expression.subroutine.extraInfo
    return info is None or (type(info).__name__ == "IteratorCallInfo"
                            and _case_source_expression_ok(info.iterExpr, packed_members=True))


def _array_reduction_terms(sm, expression, shape):
    name, width, _two_state, left, right = shape
    info = expression.subroutine.extraInfo
    parts = []
    for position in range(left, right + (1 if right >= left else -1), 1 if right >= left else -1):
        value = signed_metadata({"kind": "Ident", "span": node_span(sm, expression),
                                 "name": f"{name}[{position}]", "width": width},
                                expression.arguments[0].type.canonicalType.elementType)
        if info is not None:
            previous = dict(_ARRAY_REDUCTION_VALUES)
            _ARRAY_REDUCTION_VALUES[info.iterVar] = value
            try:
                value = convert_expr(sm, info.iterExpr)
            finally:
                _ARRAY_REDUCTION_VALUES.clear()
                _ARRAY_REDUCTION_VALUES.update(previous)
        parts.append(value)
    return parts


def _balanced_array_reduction(sm, expression, parts):
    operator = {"sum": "+", "product": "*", "and": "&", "or": "|", "xor": "^"}[
        expression.subroutineName]
    while len(parts) > 1:
        combined = []
        for index in range(0, len(parts), 2):
            combined.append(parts[index] if index + 1 == len(parts) else {
                "kind": "Binary", "span": node_span(sm, expression),
                "width": expression.type.bitWidth, "op": operator,
                "left": parts[index], "right": parts[index + 1]})
        parts = combined
    return parts[0]


def _convert_array_reduction(sm, expression):
    """IEEE 7.12.3: fold at the element / with-expression's intrinsic width."""
    if _SYM is not None or not _array_reduction_source_ok(expression):
        return unsupported(sm, expression, "ArrayReduction:storage-or-effects")
    width, _, reason = type_width_2s(expression.type)
    info = expression.subroutine.extraInfo
    element = expression.arguments[0].type.canonicalType.elementType
    result_type = info.iterExpr.type if info is not None else element
    if (reason is not None or type_width_2s(result_type)[0] != width
            or bool(result_type.isSigned) != bool(expression.type.isSigned)):
        return unsupported(sm, expression, "ArrayReduction:result-type")
    parts = _array_reduction_terms(sm, expression, _fixed_array_shape(expression.arguments[0]))
    if not _case_expression_ok(parts) or any(width_of(part) != width for part in parts):
        return unsupported(sm, expression, "ArrayReduction:with-expression")
    result = _balanced_array_reduction(sm, expression, parts)
    result["array_reduction_lowered"] = expression.subroutineName
    return signed_metadata(result, expression.type)


def _dynamic_cast_call(expression):
    return (type(expression).__name__ == "CallExpression" and expression.isSystemCall
            and expression.subroutineName == "$cast")


def _dynamic_cast_target(sm, destination):
    if type(destination).__name__ != "ElementSelectExpression":
        return legacy_blocking_target(sm, destination, True)
    shape = _fixed_array_shape(destination.value)
    if shape is None:
        return legacy_blocking_target(sm, destination, True)
    name, width, _two_state, left, right = shape
    index = destination.selector
    index_width, _, reason = type_width_2s(index.type)
    converted = convert_expr(sm, index)
    if reason is not None or not _case_expression_ok(converted):
        return unsupported(sm, destination, "DynamicCast:index"), False
    minimum = -(1 << (index_width - 1)) if index.type.isSigned else 0
    maximum = (1 << (index_width - int(index.type.isSigned))) - 1
    choices = []
    for position in range(left, right + (1 if right >= left else -1), 1 if right >= left else -1):
        if minimum <= position <= maximum:
            literal = _enum_nat_literal(sm, destination, index_width, position)
            target = {"kind": "Ident", "span": node_span(sm, destination),
                      "width": width, "name": f"{name}[{position}]"}
            choices.append([literal, target])
    return {"kind": "DynamicCastArrayTarget", "width": width,
            "index": converted, "choices": choices}, True


def _dynamic_cast_store(target, value, assign):
    if target["kind"] != "DynamicCastArrayTarget":
        return assign(target, value)
    result = {"kind": "Empty", "span": None}
    for literal, cell in reversed(target["choices"]):
        equal = {"kind": "Binary", "span": None, "width": 1, "op": "===",
                 "left": target["index"], "right": literal}
        result = {"kind": "If", "span": None, "cond": equal,
                  "then": assign(cell, value), "else": result}
    return result


def _convert_dynamic_cast(sm, expression):
    arguments = list(expression.arguments)
    if (expression.bad or len(arguments) != 2 or expression.type.bitWidth != 32
            or not expression.type.isSigned):
        return unsupported(sm, expression, "DynamicCast:signature")
    output, source = arguments
    if (type(output).__name__ != "AssignmentExpression"
            or type(output.right).__name__ != "EmptyArgumentExpression"):
        return unsupported(sm, expression, "DynamicCast:output")
    destination = output.left
    width, two_state, reason = type_width_2s(destination.type)
    if (reason is not None or type_width_2s(source.type)[0] is None
            or not _case_source_expression_ok(source, packed_members=True)
            or not _case_source_expression_ok(destination, packed_members=True)):
        return unsupported(sm, expression, "DynamicCast:type-or-effects")
    target, admitted = _dynamic_cast_target(sm, destination)
    if not admitted:
        return unsupported(sm, expression, "DynamicCast:target")
    value = convert_expr(sm, source)
    value = {"kind": "SignedResize" if source.type.isSigned else "Resize",
             "span": node_span(sm, expression), "width": width, "operand": value}
    if two_state:
        value = squash2_wrap(value, width)
    enum = destination.type.canonicalType
    members = ([_enum_literal(sm, expression, destination.type, member.value.value)
                for member in _enum_members(enum)] if type(enum).__name__ == "EnumType" else None)
    if not _case_expression_ok([value, target, members]):
        return unsupported(sm, expression, "DynamicCast:operand")
    return {"kind": "DynamicCastExpr", "span": node_span(sm, expression),
            "width": 32, "signed": True, "target": target, "value": value,
            "members": members, "dynamic_cast_lowered": True}


def _lower_dynamic_cast(node, fresh, zero, assign, block):
    result, result_decl = fresh(zero(32), prefix="$cast:")
    source, source_decl = fresh(node["value"], prefix="$cast:")
    valid = dict(zero(1), bits="1")
    if node["members"] is not None:
        valid = zero(1)
        for member in node["members"]:
            equal = {"kind": "Binary", "span": None, "width": 1,
                     "op": "===", "left": source, "right": member}
            valid = {"kind": "Binary", "span": None, "width": 1,
                     "op": "||", "left": valid, "right": equal}
    success = block([_dynamic_cast_store(node["target"], source, assign),
                     assign(result, dict(zero(32), bits="0"*31+"1"))])
    failure = ({"kind": "Unsupported", "span": node.get("span"),
                "sv_kind": "DynamicCast:task-diagnostic",
                "text": "invalid task-form cast requires runtime diagnostic observation"}
               if node.get("task") else None)
    branch = {"kind": "If", "span": node.get("span"), "cond": valid,
              "then": success, "else": failure, "dynamic_cast_lowered": True}
    return [result_decl, source_decl, branch], result


def _plusargs_call(expression):
    return (type(expression).__name__ == "CallExpression" and expression.isSystemCall
            and expression.subroutineName in ("$test$plusargs", "$value$plusargs"))


def _convert_plusargs_call(sm, expression):
    """Preserve immutable input queries; never inspect the extractor's argv."""
    args = list(expression.arguments)
    test = expression.subroutineName == "$test$plusargs"
    if (len(args) != (1 if test else 2) or expression.type.bitWidth != 32
            or not expression.type.isSigned):
        return unsupported(sm, expression, "Plusargs:signature")
    fmt = args[0]
    while type(fmt).__name__ == "ConversionExpression" and fmt.conversionKind in (
            ConversionKind.Implicit, ConversionKind.Propagated):
        fmt = fmt.operand
    if (type(fmt).__name__ != "StringLiteral" or _contains_disputed_string_escape(fmt)
            or any(ord(c) == 0 or ord(c) > 127 for c in fmt.value)):
        return unsupported(sm, expression, "Plusargs:literal-format")
    result = {"kind": "TestPlusargs" if test else "ValuePlusargsExpr",
              "span": node_span(sm, expression), "width": 32, "signed": True,
              "format": fmt.value, "plusargs_lowered": True}
    if test:
        return result
    prefix, separator, code = fmt.value.partition("%")
    if code.startswith("0"):
        code = code[1:]
    if not separator or len(code) != 1 or code.lower() not in "bodhx":
        return unsupported(sm, expression, "Plusargs:integral-format")
    arg = args[1]
    if (type(arg).__name__ != "AssignmentExpression"
            or type(arg.right).__name__ != "EmptyArgumentExpression"
            or not _case_source_expression_ok(arg.left)):
        return unsupported(sm, expression, "Plusargs:output-effects")
    target, admitted = legacy_blocking_target(sm, arg.left, True)
    if not admitted:
        return unsupported(sm, expression, "Plusargs:packed-output")
    result["target"] = target
    return result


def _has_stateful_expression(node):
    if isinstance(node, dict):
        return node.get("kind") in ("ValuePlusargsExpr", "DynamicCastExpr") or any(
            _has_stateful_expression(value) for value in node.values())
    return isinstance(node, list) and any(_has_stateful_expression(value) for value in node)


def _lower_stateful_processes(processes):
    """Sequence stateful integral operations at their source control boundary.

    Nonlogical operands with a read/write dependency have unspecified source
    evaluation order, so they stay loud. Logical operands use the IEEE
    short-circuit rule, including evaluation of the RHS for an unknown LHS.
    """
    counter = 0

    def fresh(value, width=None, prefix="$plusargs:"):
        nonlocal counter
        counter += 1
        width = width if width is not None else width_of(value)
        if width is None or width <= 0:
            raise ValueError("integral expression width")
        name = prefix + str(counter)
        ident = {"kind": "Ident", "span": None, "name": name,
                 "width": width, "two_state": False}
        decl = {"kind": "LocalDecl", "span": None, "name": name,
                "width": width, "two_state": False, "init": value,
                ("automatic_cast" if prefix == "$cast:" else "automatic_plusargs"): True}
        return ident, decl

    def block(statements):
        return {"kind": "Block", "span": None, "stmts": statements}

    def assign(target, value):
        return {"kind": "BlockingAssign", "span": None, "target": target, "value": value}

    def zero(width):
        return {"kind": "Literal", "span": None, "width": width, "bits": "0" * width}

    def written(node):
        if isinstance(node, dict):
            if node.get("kind") in ("ValuePlusargsExpr", "DynamicCastExpr"):
                return set(_converted_ident_names(node["target"]))
            return set().union(*(written(value) for value in node.values()))
        if isinstance(node, list):
            return set().union(*(written(value) for value in node))
        return set()

    def expression(node):
        if not _has_stateful_expression(node):
            if not _case_expression_ok(node):
                raise ValueError("unsupported operand")
            return [], node
        kind = node["kind"]
        if kind == "DynamicCastExpr":
            return _lower_dynamic_cast(node, fresh, zero, assign, block)
        if kind == "ValuePlusargsExpr":
            result, declaration = fresh(zero(32))
            call = dict(node, kind="ValuePlusargs", result=result)
            return [declaration, call], result
        if kind in ("Unary", "Reduce", "Resize", "SignedResize", "Squash2"):
            prelude, operand = expression(node["operand"])
            return prelude, dict(node, operand=operand)
        if kind != "Binary":
            raise ValueError("effect context")
        left, right = node["left"], node["right"]
        lp, lv = expression(left)
        rp, rv = expression(right)
        if node["op"] not in ("&&", "||"):
            if (written(left) & set(_converted_ident_names(right)) or
                    written(right) & set(_converted_ident_names(left))):
                raise ValueError("unordered dependent operands")
            return lp + rp, dict(node, left=lv, right=rv)
        # Capture the LHS before any RHS copyback; initialize the RHS so the
        # pure evaluator may inspect both operands after a skipped call.
        captured, save_left = fresh(lv)
        rhs, save_right = fresh(zero(width_of(rv)))
        truth = {"kind": "Unary", "span": None, "width": 1, "op": "!",
                 "operand": {"kind": "Unary", "span": None, "width": 1,
                             "op": "!", "operand": captured}}
        skip = zero(1) if node["op"] == "&&" else dict(zero(1), bits="1")
        guard = {"kind": "Binary", "span": None, "width": 1, "op": "!==",
                 "left": truth, "right": skip}
        branch = {"kind": "If", "span": None, "cond": guard,
                  "then": block(rp + [assign(rhs, rv)]), "else": None}
        return lp + [save_left, save_right, branch], dict(node, left=captured, right=rhs)

    def lower(node):
        if isinstance(node, list):
            return [lower(value) for value in node]
        if not isinstance(node, dict):
            return node
        kind = node.get("kind")
        if kind == "DynamicCastStatement":
            prelude, _ = expression(node["value"])
            return block(prelude)
        field = "cond" if kind == "If" else "value" if kind == "BlockingAssign" else None
        if field is not None and _has_stateful_expression(node[field]):
            try:
                prelude, value = expression(node[field])
                rest = {key: lower(child) for key, child in node.items() if key != field}
                return block(prelude + [dict(rest, **{field: value})])
            except ValueError as error:
                return {"kind": "Unsupported", "span": node.get("span"),
                        "sv_kind": ("DynamicCast" if _node_marker(node, "dynamic_cast_lowered")
                                    else "Plusargs") + ":expression-effects", "text": str(error)}
        if kind == "DynamicCastExpr":
            return {"kind": "Unsupported", "span": node.get("span"),
                    "sv_kind": "DynamicCast:expression-context", "text": "stateful dynamic cast"}
        if kind == "ValuePlusargsExpr":
            return {"kind": "Unsupported", "span": node.get("span"),
                    "sv_kind": "Plusargs:statement-context", "text": "stateful input query"}
        return {key: lower(value) for key, value in node.items()}

    return lower(processes)


def _case_skip_call_purity(node, packed_members):
    if _SYM is None and _clog2_call(node):
        return len(node.arguments) == 1 and all(
            _case_source_expression_ok(argument, packed_members=packed_members)
            for argument in node.arguments)
    if _SYM is None and _array_reduction_call(node):
        return _array_reduction_source_ok(node)
    if type(node).__name__ == "CallExpression" and _enum_method_call(node):
        return _SYM is None and all(
            _case_source_expression_ok(argument, packed_members=True)
            for argument in node.arguments)
    return None


def _case_source_expression_ok(expression, *, packed_members=False):
    """Check bound source operands before constant folding can erase effects."""
    pure = True

    def check(node):
        nonlocal pure
        kind = type(node).__name__
        skipped_call = _case_skip_call_purity(node, packed_members)
        if skipped_call is not None:
            pure = pure and skipped_call
            return VisitAction.Skip
        if (_SYM is None and kind == "HierarchicalValueExpression"
                and (node.symbol in _ELAB_HIER_VALUES or node.symbol in _ELAB_PARAMETERS)):
            return
        if (_SYM is None and _plusargs_call(node)
                and node.subroutineName == "$test$plusargs"):
            return VisitAction.Skip
        if kind == "CallExpression" and _fixed_bits_query_width(node) is not None:
            return VisitAction.Skip
        if kind == "CallExpression" and _bit_query_call(node):
            pure = pure and all(type_width_2s(argument.type)[0] is not None
                                for argument in node.arguments)
            return
        if kind == "CallExpression" and _signing_call(node):
            pure = pure and _signing_signature_ok(node)
            return
        if kind == "MemberAccessExpression" and packed_members:
            container = node.value.type.canonicalType
            if type(container).__name__ in ("PackedStructType", "PackedUnionType"):
                pure = pure and not getattr(container, "isTagged", False)
            elif type(container).__name__ == "UnpackedStructType":
                pure = pure and _unpacked_struct_member(None, node) is not None
            else:
                pure = False
            return
        pure = pure and not getattr(node, "bad", False) and kind in (
            "IntegerLiteral", "UnbasedUnsizedIntegerLiteral", "StringLiteral",
            "NamedValueExpression", "ConversionExpression", "UnaryExpression",
            "BinaryExpression", "ConditionalExpression", "ConcatenationExpression",
            "SimpleAssignmentPatternExpression", "StructuredAssignmentPatternExpression",
            "ReplicatedAssignmentPatternExpression", "ReplicationExpression",
            "ElementSelectExpression", "RangeSelectExpression",
            "InsideExpression", "ValueRangeExpression", "UnboundedLiteral", "MinTypMaxExpression",
        )
        if kind == "UnaryExpression":
            pure = pure and (node.op in UNARY_OPS or node.op in REDUCE_OPS)
        if kind == "BinaryExpression":
            pure = pure and (node.op in BINARY_OPS or node.op == BinaryOperator.LogicalImplication)

    _visit_selected_expression(expression, check)
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
    """Pure IEEE 12.5/12.5.1/12.5.4 cases, with whole-case sizing."""
    if stmt.check != UniquePriorityCheck.None_:
        return unsupported(sm, stmt, "CaseStatement:" + str(stmt.check).split(".")[-1])
    condition = str(stmt.condition).split(".")[-1]
    modes = {"Normal": None, "WildcardJustZ": "casez", "WildcardXOrZ": "casex"}
    if condition not in modes and condition != "Inside":
        return unsupported(sm, stmt, "CaseStatement:" + condition)
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
            if condition == "Inside":
                comparisons = _inside_item(
                    sm, expression, subject, width, stmt.expr.type.isSigned,
                    allow_unbounded=False, allow_array_widening=False)
                if not comparisons:
                    return unsupported(sm, stmt, "CaseStatement:pattern")
            else:
                pattern = convert_expr(sm, expression)
                pattern_width, _, _ = type_width_2s(expression.type)
                if (pattern_width != width or width_of(pattern) != width
                        or not _case_expression_ok(pattern)):
                    return unsupported(sm, stmt, "CaseStatement:pattern")
                comparison = {"kind": "Binary", "span": node_span(sm, stmt), "width": 1,
                              "op": "===", "left": subject, "right": pattern}
                if modes[condition] is not None:
                    comparison = {"kind": "CaseMatch", "span": node_span(sm, stmt), "width": 1,
                                  "mode": modes[condition], "left": subject, "right": pattern}
                comparisons = [comparison]
            branches.extend((comparison, body) for comparison in comparisons)
    if not branches:
        return unsupported(sm, stmt, "CaseStatement:empty")
    result = convert_stmt(sm, stmt.defaultCase) if stmt.defaultCase is not None else None
    span = node_span(sm, stmt)
    for comparison, body in reversed(branches):
        result = {
            "kind": "If", "span": span, "case_lowered": True,
            "cond": comparison,
            "then": body, "else": result,
        }
    return result


def _convert_test_loop(sm, statement, kind):
    if _SYM is not None:
        return unsupported(sm, statement)
    width, _, reason = type_width_2s(statement.cond.type)
    if width is None or reason is not None or not _case_source_expression_ok(statement.cond):
        return unsupported(sm, statement, kind + ":condition")
    condition = convert_expr(sm, statement.cond)
    if not _case_expression_ok(condition):
        return unsupported(sm, statement, kind + ":condition")
    body = convert_stmt(sm, statement.body)
    if contains_local_decl(body):
        return unsupported(sm, statement, kind + ":body-lifetime")
    return {"kind": "While" if kind == "WhileLoopStatement" else "DoWhile",
            "span": node_span(sm, statement), "condition": condition, "body": body}


def _convert_foreach_loop(sm, statement):
    """IEEE 12.7.3: one ordinal loop, so break exits every named dimension.

    Fixed bounds are elaboration data; element reads in the body stay live.
    Mixed-radix offsets give the rightmost named dimension unit stride.
    Omitting every dimension has cardinality one, as an empty product.
    """
    if _SYM is not None:
        return unsupported(sm, statement)
    source = statement.arrayRef
    width, _, reason = type_width_2s(source.type)
    if (not _storage_expression(source)
            or str(source.symbol.kind) != "SymbolKind.Variable"
            or (_fixed_array_shape(source) is None and
                (reason is not None or width is None
                 or type(source.type.canonicalType).__name__ != "PackedArrayType"))):
        return unsupported(sm, statement, "ForeachLoopStatement:array")
    dimensions = []
    total = 1
    for dimension in statement.loopDims:
        if dimension.range is None:
            return unsupported(sm, statement, "ForeachLoopStatement:dimension")
        if dimension.loopVar is None:
            continue
        variable = dimension.loopVar
        if variable.type.bitWidth != 32 or not variable.type.isSigned:
            return unsupported(sm, statement, "ForeachLoopStatement:iterator-type")
        left, right = int(dimension.range.left), int(dimension.range.right)
        size = abs(left - right) + 1
        total *= size
        if total >= 1 << 32:
            return unsupported(sm, statement, "ForeachLoopStatement:cardinality")
        dimensions.append((_foreach_storage_name(variable), left, right, size))
    body = convert_stmt(sm, statement.body)
    if contains_local_decl(body):
        return unsupported(sm, statement, "ForeachLoopStatement:body-lifetime")
    span = node_span(sm, statement)
    cursor_name = _scoped_temp("$foreach:", statement.sourceRange.start.offset, ":$ordinal")

    def literal(value):
        return {"kind": "Literal", "span": span, "width": 32,
                "bits": format(value & 0xffffffff, "032b")}

    def ident(name, signed=False):
        return {"kind": "Ident", "span": span, "width": 32,
                "name": name, "signed": signed}

    def binary(op, left, right, width=32):
        return {"kind": "Binary", "span": span, "width": width,
                "op": op, "left": left, "right": right}

    def assign(name, value):
        return {"kind": "BlockingAssign", "span": span,
                "target": ident(name), "value": value}

    declarations = [{"kind": "LocalDecl", "span": span, "width": 32,
                     "name": name, "two_state": name == cursor_name,
                     "signed": name != cursor_name, "init": None,
                     "automatic_foreach": True}
                    for name in [cursor_name] + [d[0] for d in dimensions]]
    bindings = []
    stride = total
    for name, left, right, size in dimensions:
        stride //= size
        offset = binary("u%", binary("u/", ident(cursor_name), literal(stride)),
                        literal(size))
        value = binary("+" if left <= right else "-", literal(left), offset)
        bindings.append(assign(name, value))
    loop = {"kind": "For", "span": span, "foreach_lowered": True,
            "foreach_dimensions": [{"name": name, "left": left, "right": right}
                                   for name, left, right, _ in dimensions],
            "initializers": [assign(cursor_name, literal(0))],
            "condition": binary("<", ident(cursor_name), literal(total), 1),
            "steps": [assign(cursor_name, binary("+", ident(cursor_name), literal(1)))],
            "body": {"kind": "Block", "span": span, "stmts": bindings + [body]}}
    return {"kind": "Block", "span": span, "stmts": declarations + [loop]}


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


def _convert_immediate_assertion(sm, statement):
    """Simple immediate checks use ordinary conditional action execution.

    A missing assert/assume failure action requests the standard's implicit
    error diagnostic. Keep that branch loud rather than erasing the effect.
    Deferred checks require observation-region semantics, not an ordinary If.
    """
    if _SYM is not None:
        return unsupported(sm, statement, "ImmediateAssertion:symbolic")
    if statement.isDeferred:
        return unsupported(sm, statement, "ImmediateAssertion:deferred")
    if (statement.ifFalse is not None
            and type(statement.ifFalse).__name__ == "EmptyStatement"):
        return unsupported(sm, statement, "ImmediateAssertion:null-failure")
    assertion = str(statement.assertionKind).split(".")[-1]
    names = {"Assert": "assert", "Assume": "assume", "CoverProperty": "cover"}
    if assertion not in names:
        return unsupported(sm, statement, "ImmediateAssertion:kind")
    condition = convert_expr(sm, statement.cond)
    if (not _case_source_expression_ok(statement.cond)
            or not _case_expression_ok(condition)):
        return unsupported(sm, statement, "ImmediateAssertion:condition")
    success = (convert_stmt(sm, statement.ifTrue) if statement.ifTrue is not None
               else {"kind": "Empty", "span": None})
    if statement.ifFalse is not None:
        failure = convert_stmt(sm, statement.ifFalse)
    elif assertion == "CoverProperty":
        failure = None
    else:
        failure = unsupported(sm, statement, "ImmediateAssertion:implicit-error",
                              "implicit assertion failure diagnostic")
    return {"kind": "If", "span": node_span(sm, statement), "cond": condition,
            "then": success, "else": failure,
            "immediate_assertion": names[assertion], "assertion_lowered": True}


def contains_local_decl(node):
    if isinstance(node, dict):
        return (node.get("kind") == "LocalDecl"
                and not node.get("automatic_array", False)
                and not node.get("automatic_scalar", False)
                and not node.get("automatic_foreach", False)
                and not node.get("automatic_intra", False)
                and not node.get("automatic_compound", False)) or any(
            contains_local_decl(value) for value in node.values())
    if isinstance(node, list):
        return any(contains_local_decl(value) for value in node)
    return False


def _scan_call(expression):
    while type(expression).__name__ == "ConversionExpression" and expression.conversionKind in (
            ConversionKind.Implicit, ConversionKind.Propagated):
        expression = expression.operand
    if (type(expression).__name__ == "CallExpression" and expression.isSystemCall
            and expression.subroutineName == "$sscanf"):
        return expression
    return None


def _scan_format_count(text):
    """Admission only; the shared Lean scanner interprets the format."""
    position, outputs = 0, 0
    while position < len(text):
        if text[position] != "%":
            if ord(text[position]) == 0 or ord(text[position]) > 127:
                return None
            position += 1
            continue
        position += 1
        if position < len(text) and text[position] == "%":
            position += 1
            continue
        suppressed = position < len(text) and text[position] == "*"
        if suppressed:
            position += 1
        start = position
        while position < len(text) and "0" <= text[position] <= "9":
            position += 1
        if start != position and int(text[start:position]) == 0:
            return None
        if position == len(text) or text[position].lower() not in "bodhxcsv":
            return None
        outputs += not suppressed
        position += 1
    return outputs


def _convert_scan_assignment(sm, expression):
    call = _scan_call(expression.right)
    if call is None:
        return None
    if _SYM is not None or expression.isNonBlocking or expression.op is not None:
        return unsupported(sm, expression, "Scanf:assignment-context")
    arguments = list(call.arguments)
    if len(arguments) < 2 or call.type.bitWidth != 32 or not call.type.isSigned:
        return unsupported(sm, call, "Scanf:signature")
    source, format_expr = arguments[:2]
    if (type(format_expr).__name__ != "StringLiteral"
            or _contains_disputed_string_escape(format_expr)):
        return unsupported(sm, call, "Scanf:format")
    count = _scan_format_count(format_expr.value)
    if count is None or count != len(arguments) - 2:
        return unsupported(sm, call, "Scanf:format-or-arity")
    if not _case_source_expression_ok(source):
        return unsupported(sm, call, "Scanf:input-effects")
    if type(source).__name__ == "StringLiteral":
        text = source.value
        if (any(ord(c) > 127 for c in text)
                or _contains_disputed_string_escape(source)
                or source.type.bitWidth != max(8, len(text) * 8)):
            return unsupported(sm, call, "Scanf:input-encoding")
        width = max(8, len(text) * 8)
        value = int.from_bytes(text.encode("ascii"), "big")
        input_node = {"kind": "Literal", "span": node_span(sm, source),
                      "width": width, "bits": format(value, "0%db" % width)}
    else:
        width, _, reason = type_width_2s(source.type)
        input_node = convert_expr(sm, source)
        if reason is not None or width is None or not _case_expression_ok(input_node):
            return unsupported(sm, call, "Scanf:input-type")
    outputs = []
    for argument in arguments[2:]:
        if (type(argument).__name__ != "AssignmentExpression"
                or type(argument.right).__name__ != "EmptyArgumentExpression"
                or not _case_source_expression_ok(argument.left)):
            return unsupported(sm, call, "Scanf:output-effects")
        target, admitted = legacy_blocking_target(sm, argument.left, True)
        if not admitted:
            return unsupported(sm, call, "Scanf:output-target")
        outputs.append(target)
    if not _case_source_expression_ok(expression.left):
        return unsupported(sm, call, "Scanf:result-effects")
    result, admitted = legacy_blocking_target(sm, expression.left, True)
    if not admitted:
        return unsupported(sm, call, "Scanf:result-target")
    return {"kind": "Scanf", "span": node_span(sm, expression), "input": input_node,
            "format": format_expr.value, "outputs": outputs, "result": result,
            "scanf_lowered": True}


def _compound_value(sm, expression, read):
    global _COMPOUND_READ
    previous = _COMPOUND_READ
    _COMPOUND_READ = read
    try:
        value = convert_expr(sm, expression.right)
    finally:
        _COMPOUND_READ = previous
    if not expression.left.type.isFourState:
        value = squash2_wrap(value, expression.left.type.bitWidth)
    return value


def _has_compound_assignment(comp):
    found = False
    def inspect(node):
        nonlocal found
        found = found or (type(node).__name__ == "AssignmentExpression"
                          and node.op is not None)
    comp.getRoot().visit(inspect)
    return found


def _expression_without_spans(node):
    if isinstance(node, dict):
        return {key: _expression_without_spans(value) for key, value in node.items()
                if key != "span"}
    if isinstance(node, list):
        return [_expression_without_spans(value) for value in node]
    return node


def _unchanged_compound(sm, expression, read, value, span):
    """Retain old envelopes only when their complete expression trees agree."""
    if read.get("kind") != "Ident":
        return None
    symbol = BINARY_OPS.get(expression.op)
    rhs = _compound_rhs(expression.right)
    right = convert_expr(sm, rhs)
    width = expression.type.bitWidth
    if not _binary_width_ok(symbol, width, width_of(read), width_of(right)):
        return None
    if symbol in ("/", "%"):
        symbol = ("s" if expression.left.type.isSigned and rhs.type.isSigned else "u") + symbol
    if symbol in ("<<", ">>", "<<<", ">>>"):
        symbol = ("s" if expression.left.type.isSigned else "u") + symbol
    old = {"kind": "Binary", "span": node_span(sm, expression), "width": width,
           "op": symbol, "left": read, "right": right}
    if not expression.left.type.isFourState:
        old = squash2_wrap(old, width)
    if _expression_without_spans(old) != _expression_without_spans(value):
        return None
    return {"kind": "BlockingAssign", "span": span, "target": read, "value": old}


def _convert_compound_assignment(sm, expression, span_node=None):
    """IEEE 11.4.1: capture selectors once and retain the bound RMW tree."""
    if (_SYM is not None or expression.isNonBlocking
            or BINARY_OPS.get(expression.op) not in
            ("+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "<<<", ">>>")):
        return unsupported(sm, span_node or expression, "AssignmentExpression:compound")
    lhs, rhs = expression.left, _compound_rhs(expression.right)
    width, _, reason = type_width_2s(lhs.type)
    references = []
    _visit_selected_expression(expression.right, lambda node: references.append(node)
                               if type(node).__name__ == "LValueReferenceExpression" else None)
    if (reason is not None or width is None or len(references) != 1
            or references[0].type.bitWidth != width
            or not _case_source_expression_ok(lhs, packed_members=True)
            or not _case_source_expression_ok(rhs, packed_members=True)):
        return unsupported(sm, expression, "AssignmentExpression:compound-source")
    span = node_span(sm, span_node or expression)
    read = convert_expr(sm, lhs)
    if read.get("kind") == "Ident":
        value = _compound_value(sm, expression, read)
        unchanged = _unchanged_compound(sm, expression, read, value, span)
        if unchanged is not None:
            return unchanged
    prefix = []

    def capture(value, suffix):
        name = _scoped_temp("$compound:", expression.sourceRange.start.offset, suffix)
        prefix.append({"kind": "LocalDecl", "span": span, "width": width_of(value),
                       "name": name, "two_state": False, "init": value,
                       "automatic_compound": True})
        return {"kind": "Ident", "span": None, "width": width_of(value), "name": name}

    def assign(target, value):
        return {"kind": "BlockingAssign", "span": span, "target": target, "value": value}

    def selected_read(target):
        return {key: ("CompoundRead" if key == "kind" else value)
                for key, value in target.items() if key != "two_state"}

    array = _fixed_array_shape(lhs.value) if type(lhs).__name__ == "ElementSelectExpression" else None
    if array is not None:
        name, element_width, two_state, left, right = array
        index = convert_expr(sm, lhs.selector)
        index_width, _, index_reason = type_width_2s(lhs.selector.type)
        if (index_reason is not None or index_width is None
                or not _case_expression_ok(index) or width_of(index) != index_width):
            return unsupported(sm, expression, "AssignmentExpression:compound-index")
        index = capture(index, ":index")
        minimum = -(1 << (index_width - 1)) if lhs.selector.type.isSigned else 0
        maximum = (1 << (index_width - int(lhs.selector.type.isSigned))) - 1
        positions = [position for position in range(left, right + (1 if right >= left else -1),
                                                   1 if right >= left else -1)
                     if minimum <= position <= maximum]
        branches = []
        read = {"kind": "Literal", "span": span, "width": element_width,
                "bits": ("0" if two_state else "x") * element_width}
        for position in positions:
            target = {"kind": "Ident", "span": node_span(sm, lhs),
                      "width": element_width, "name": f"{name}[{position}]"}
            literal = {"kind": "Literal", "span": span, "width": index_width,
                       "bits": format(position & ((1 << index_width) - 1), f"0{index_width}b")}
            comparison = {"kind": "Binary", "span": span, "width": 1, "op": "===",
                          "left": index, "right": literal}
            branches.append((comparison, target))
        for comparison, target in reversed(branches):
            read = {"kind": "Ternary", "span": span, "width": element_width,
                    "cond": comparison, "then": target, "else": read}
        value = _compound_value(sm, expression, read)
        if width_of(value) != width or not _case_expression_ok(value):
            return unsupported(sm, expression, "AssignmentExpression:compound-value")
        value = capture(value, ":value")
        result = {"kind": "Empty", "span": span}
        for comparison, target in reversed(branches):
            result = {"kind": "If", "span": span, "cond": comparison,
                      "then": assign(target, value), "else": result}
        return {"kind": "Block", "span": span, "stmts": prefix + [result],
                "compound_assignment_lowered": True}
    target, admitted = legacy_blocking_target(sm, lhs, True)
    suffix = []
    if not admitted and type(lhs).__name__ in ("ElementSelectExpression", "RangeSelectExpression"):
        member = lhs.value
        shape = _packed_struct_member(sm, member)
        selection = str(getattr(lhs, "selectionKind", "")).split(".")[-1]
        if (shape is not None and _canonical_packed_select_source(member.type)
                and (type(lhs).__name__ == "ElementSelectExpression"
                     or selection in ("IndexedUp", "IndexedDown"))):
            member_target, member_ok = legacy_blocking_target(sm, member, True)
            member_read = convert_expr(sm, member)
            position = lhs.selector if type(lhs).__name__ == "ElementSelectExpression" else lhs.left
            index = convert_expr(sm, position)
            if member_ok and _case_expression_ok([member_read, index]):
                index = capture(index, ":index")
                captured = capture(member_read, ":member")
                target = {"kind": "SelectTarget", "span": span, "width": width,
                          "value": captured, "index": index,
                          "index_signed": bool(position.type.isSigned),
                          "descending": selection == "IndexedDown",
                          "two_state": not lhs.type.isFourState}
                suffix = [assign(member_target, captured)]
                admitted = True
    if not admitted or target.get("kind") not in ("Ident", "SelectTarget"):
        return unsupported(sm, expression, "AssignmentExpression:compound-target")
    if target["kind"] == "SelectTarget":
        target = dict(target)
        if not suffix and target["index"].get("kind") != "Literal":
            target["index"] = capture(target["index"], ":index")
        read = selected_read(target)
    else:
        read = convert_expr(sm, lhs)
    value = _compound_value(sm, expression, read)
    if (width_of(value) != width or not _case_expression_ok([target, read, value])):
        return unsupported(sm, expression, "AssignmentExpression:compound-value")
    statements = prefix + [assign(target, value)] + suffix
    if len(statements) == 1:
        return dict(statements[0], compound_assignment_lowered=True)
    return {"kind": "Block", "span": span, "stmts": statements,
            "compound_assignment_lowered": True}


def _convert_assignment_expr(sm, expr, span_node=None):
    if type(expr).__name__ != "AssignmentExpression":
        return unsupported(sm, span_node or expr,
                           "AssignmentExpression:" + type(expr).__name__)
    if expr.timingControl is not None:
        return _convert_intra_assignment(sm, expr)
    scan = _convert_scan_assignment(sm, expr)
    if scan is not None:
        return scan
    if expr.op is None:
        streaming_target = (
            _symbolic_streaming_target_assignment(sm, expr)
            if _SYM is not None else _streaming_target_assignment(sm, expr))
        if streaming_target is not None:
            return streaming_target
    if expr.op is None and _SYM is None:
        array_pattern_lhs = _fixed_array_pattern_lhs_assignment(sm, expr)
        if array_pattern_lhs is not None:
            return array_pattern_lhs
        array_slice = _fixed_array_slice_pattern_assignment(sm, expr)
        if array_slice is not None:
            return array_slice
        array_concat = _fixed_array_concat_assignment(sm, expr)
        if array_concat is not None:
            return array_concat
        array_conditional = _fixed_array_conditional_assignment(sm, expr)
        if array_conditional is not None:
            return array_conditional
        array_copy = _fixed_array_copy_assignment(sm, expr)
        if array_copy is not None:
            return array_copy
        dynamic_array = _fixed_array_dynamic_assignment(sm, expr)
        if dynamic_array is not None:
            return dynamic_array
        array_assignment = _fixed_array_pattern_assignment(sm, expr)
        if array_assignment is not None:
            return array_assignment
    if expr.op is not None:
        return _convert_compound_assignment(sm, expr, span_node)
    if (_SYM is None and _fixed_array_oob_select(sm, expr.left)
            and _case_source_expression_ok(expr.right)):
        # IEEE 1800 §7.4.5: an invalid unpacked-array index performs no
        # update. The admitted RHS subset is pure, so dropping the write
        # preserves its value semantics without inventing an aggregate store.
        value = convert_expr(sm, expr.right)
        if value is not None and _case_expression_ok(value):
            return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                    "oob_write_noop": True}
    if _SYM is None:
        target, ok = legacy_blocking_target(sm, expr.left)
    else:
        target, ok = select_target(sm, expr.left)
    if not ok:
        return unsupported(sm, span_node or expr, "AssignmentExpression:target")
    if (target.get("kind") in ("SelectTarget", "ConcatTarget")
            and not _case_source_expression_ok(expr.right, packed_members=_SYM is None)):
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
    if _SYM is None and _automatic_default_gap(symbol):
        return unsupported(sm, stmt, "AutomaticLocal:default-lifetime",
                           "implicit procedural lifetime in an automatic module is not qualified")
    if _SYM is None and str(symbol.lifetime).split(".")[-1] == "Static":
        # The module's declaration-identity pass initializes static storage
        # before any process starts, including in blocks never entered.
        return {"kind": "Empty", "span": node_span(sm, stmt)}
    if _SYM is None:
        cells = convert_fixed_array_vars(sm, symbol)
        if cells is not None:
            lifetime = str(symbol.lifetime).split(".")[-1]
            if lifetime == "Automatic":
                array_shape = _fixed_array_dimensions(symbol.type)
                if array_shape is None:
                    return unsupported(sm, stmt, "VariableDeclStatement:array-type")
                _array_dimensions, element_type = array_shape
                return {"kind": "Block", "span": node_span(sm, stmt), "stmts": [
                    {"kind": "LocalDecl", "span": cell["span"], "name": cell["name"],
                     "width": cell["width"], "signed": cell.get("signed", False),
                     "two_state": not element_type.isFourState, "init": cell["init"],
                     "automatic_array": True} for cell in cells]}
            return unsupported(sm, stmt, "VariableDeclStatement:array-lifetime")
    width, two_state, reason = type_width_2s(symbol.type)
    if width is None:
        if reason == "type" and not getattr(symbol.type, "isFourState", True):
            reason = "2state"
        return unsupported(sm, stmt, "VariableDeclStatement:" + reason)
    initializer = getattr(symbol, "initializer", None)
    init_node = convert_expr(sm, initializer) if initializer is not None else None
    if two_state and init_node is not None:
        init_node = squash2_wrap(init_node, width)
    declaration = signed_metadata({
        "kind": "LocalDecl",
        "span": node_span(sm, stmt),
        "name": _storage_name(symbol),
        "width": width,
        "two_state": two_state,
        "init": init_node,
    }, symbol.type)
    if _SYM is None and str(symbol.lifetime).split(".")[-1] == "Automatic":
        declaration["automatic_scalar"] = True
    return declaration


def _convert_syscall(sm, s, e):
    """`$display`/`$write`/`$finish`/`$stop` in statement position ->
    `SysCall` node (self-check tier §f). `$display`/`$write` require the
    first argument to be a string literal (the format); the remaining args
    are M0/self-check expressions with a parallel `arg_signed` list (the
    Lean renderer needs signedness for `%d` widths and refuses to print
    negative signed values — the envelope carries no sign). `$finish`/
    `$stop` arguments (verbosity levels) are ignored. Any other call stays
    `Unsupported` (statement tag `ExpressionStatement:CallExpression`)."""
    if _SYM is None and _dynamic_cast_call(e):
        value = _convert_dynamic_cast(sm, e)
        if value.get("kind") == "Unsupported":
            return value
        return {"kind": "DynamicCastStatement", "span": node_span(sm, s),
                "value": dict(value, task=True)}
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
    if (_SYM is None and pk == ProceduralBlockKind.Always
            and not (type(body).__name__ == "TimedStatement"
                     and type(body.timing).__name__ == "SignalEventControl"
                     and body.timing.edge == EdgeKind.PosEdge)):
        converted = convert_stmt(sm, body)
        if contains_local_decl(converted):
            return unsupported(sm, m, "Always:body-lifetime")
        return {"kind": "Always", "span": span, "body": converted,
                "always_lowered": True}
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


def _symbolic_concat_target(sm, lhs):
    """Lower a continuous-assignment concatenation to direct target leaves.

    The semantic tier already owns continuous comb settling and fixed
    select windows.  This surface form only admits a statically sized,
    duplicate-free concatenation of those leaves, and requires the RHS to
    have no target-name alias so splitting it into windows preserves the
    single sampled RHS rule.  Aggregate, dynamic and aliased forms remain
    loud until their storage/driver contracts are explicit.
    """
    if type(lhs).__name__ != "ConcatenationExpression":
        return None

    def leaves(node):
        if type(node).__name__ == "ConcatenationExpression":
            out = []
            for operand in node.operands:
                nested = leaves(operand)
                if nested is None:
                    return None
                out.extend(nested)
            return out
        node_kind = type(node).__name__
        if node_kind == "ElementSelectExpression":
            if _constant_dimension_selector(node.selector) is None:
                return None
        elif node_kind == "RangeSelectExpression":
            if (str(node.selectionKind).split(".")[-1] != "Simple"
                    or _constant_dimension_selector(node.left) is None
                    or _constant_dimension_selector(node.right) is None):
                return None
        target, admitted = select_target(sm, node)
        if not admitted or target is None:
            return None
        if target.get("kind") not in ("Ident", "BitSel", "PartSel"):
            return None
        if target.get("kind") != "Ident":
            base = target.get("value")
            if base is None or base.get("kind") != "Ident":
                return None
        if target.get("width", 0) <= 0:
            return None
        if target.get("kind") == "Ident":
            window = (target.get("name"), None, None)
        else:
            base = target.get("value", {}).get("name")
            if target.get("kind") == "BitSel":
                index = target.get("index", {})
                if index.get("kind") != "Int":
                    return None
                window = (base, index.get("value"), index.get("value"))
            else:
                left = target.get("msb", {}).get("value")
                right = target.get("lsb", {}).get("value")
                if (target.get("msb", {}).get("kind") != "Int" or
                        target.get("lsb", {}).get("kind") != "Int"):
                    return None
                window = (base, min(left, right), max(left, right))
        target["_window"] = window
        return [target]

    parts = leaves(lhs)
    if not parts:
        return None
    seen = set()
    windows = []
    for target in parts:
        window = target.pop("_window", None)
        key = json.dumps(target, sort_keys=True, separators=(",", ":"))
        if key in seen:
            return None
        seen.add(key)
        if window is not None:
            base, low, high = window
            for old_base, old_low, old_high in windows:
                if old_base != base:
                    continue
                if low is None or old_low is None or not (high < old_low or old_high < low):
                    return None
            windows.append(window)
    return parts


def _converted_ident_names(node):
    if isinstance(node, dict):
        names = set()
        if node.get("kind") == "Ident" and node.get("name") is not None:
            names.add(node["name"])
        for value in node.values():
            names.update(_converted_ident_names(value))
        return names
    if isinstance(node, list):
        names = set()
        for value in node:
            names.update(_converted_ident_names(value))
        return names
    return set()


def _symbolic_target_windows(target):
    """Return statically known `(base, low, high)` windows for a target."""
    if not isinstance(target, dict):
        return None
    kind = target.get("kind")
    if kind == "ConcatTarget":
        windows = []
        for part in target.get("parts", []):
            nested = _symbolic_target_windows(part)
            if nested is None:
                return None
            windows.extend(nested)
        return windows
    if kind == "Ident":
        width = target.get("width")
        name = target.get("name")
        if not isinstance(width, int) or width <= 0 or not name:
            return None
        return [(name, 0, width - 1)]
    if kind == "BitSel":
        base = target.get("value", {})
        index = target.get("index", {})
        if base.get("kind") != "Ident" or index.get("kind") != "Int":
            return None
        name = base.get("name")
        value = index.get("value")
        return [(name, value, value)] if name and isinstance(value, int) else None
    if kind == "PartSel":
        base = target.get("value", {})
        msb = target.get("msb", {})
        lsb = target.get("lsb", {})
        if (base.get("kind") != "Ident" or msb.get("kind") != "Int"
                or lsb.get("kind") != "Int"):
            return None
        name = base.get("name")
        left, right = msb.get("value"), lsb.get("value")
        if not name or not isinstance(left, int) or not isinstance(right, int):
            return None
        return [(name, min(left, right), max(left, right))]
    if kind == "SelectTarget":
        # Legacy packed-member targets encode their constant LSB offset as a
        # literal index and carry the selected width separately. This is the
        # same flat vector window represented by symbolic PartSel nodes.
        base = target.get("value", {})
        index = target.get("index", {})
        width = target.get("width")
        bits = index.get("bits")
        if (base.get("kind") != "Ident" or index.get("kind") != "Literal"
                or not isinstance(width, int) or width <= 0
                or not isinstance(bits, str) or not bits
                or any(bit not in "01" for bit in bits)):
            return None
        name = base.get("name")
        offset = int(bits, 2)
        return [(name, offset, offset + width - 1)] if name else None
    return None


def _reject_overlapping_symbolic_drivers(processes):
    """Make statically overlapping constant continuous drivers loud."""
    windows = []
    for index, process in enumerate(processes):
        if process.get("kind") != "Assign":
            continue
        current = _symbolic_target_windows(process.get("target"))
        if current is None:
            continue
        conflict = any(
            old_base == base and not (high < old_low or old_high < low)
            for base, low, high in current
            for old_base, old_low, old_high in windows
        )
        if conflict:
            processes[index] = {
                "kind": "Unsupported",
                "span": process.get("span"),
                "sv_kind": "AssignmentExpression:target",
                "text": "overlapping constant continuous driver",
            }
        else:
            windows.extend(current)


def convert_continuous_assign(sm, m):
    if getattr(m, "delay", None) is not None:
        return unsupported(sm, m, "ContinuousAssignSymbol:delay")
    e = m.assignment
    if type(e).__name__ != "AssignmentExpression":
        return unsupported(sm, m, "ContinuousAssignSymbol:" + type(e).__name__)
    if e.op is not None or e.timingControl is not None or e.isNonBlocking:
        return unsupported(sm, m, "ContinuousAssignSymbol:form")
    streaming = type(e.left).__name__ == "StreamingConcatenationExpression"
    legacy_streaming = _SYM is None and streaming
    symbolic_streaming = _SYM is not None and streaming
    if streaming:
        lowered = (_streaming_target_assignment(sm, e)
                   if legacy_streaming else
                   _symbolic_streaming_target_assignment(sm, e))
        if lowered is None:
            return unsupported(sm, m, "AssignmentExpression:target")
        target = lowered["target"]
        value = lowered["value"]
        ok = True
    else:
        target, ok = (legacy_blocking_target(sm, e.left)
                      if _SYM is None else select_target(sm, e.left))
        if (_SYM is None and ok
                and target.get("kind") in ("SelectTarget", "ConcatTarget")
                and _symbolic_target_windows(target) is None):
            return unsupported(sm, m, "AssignmentExpression:target")
        if _SYM is not None and type(e.left).__name__ == "ConcatenationExpression":
            parts = _symbolic_concat_target(sm, e.left)
            if parts is None:
                return unsupported(sm, m, "AssignmentExpression:target")
            target = {
                "kind": "ConcatTarget",
                "span": node_span(sm, e.left),
                "width": e.left.type.bitWidth,
                "parts": parts,
            }
            ok = True
        if not ok:
            return unsupported(sm, m, "AssignmentExpression:target")
        value = convert_expr(sm, e.right)
    if (_SYM is not None and target.get("kind") == "ConcatTarget"):
        if width_of(value) != target.get("width"):
            return unsupported(sm, m, "AssignmentExpression:target")
        target_names = {
            part.get("name") if part.get("kind") == "Ident"
            else part.get("value", {}).get("name")
            for part in target.get("parts", [])
        }
        if _converted_ident_names(value) & target_names:
            return unsupported(sm, m, "AssignmentExpression:target")
    try:
        if not symbolic_streaming and not e.left.type.isFourState:
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
    struct_decls = _unpacked_struct_decls(sm, m)
    if struct_decls is not None:
        return struct_decls
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
        "name": _storage_name(m),
        "width": w,
        "init": init_d,
    }, m.type)


def convert_fixed_array_vars(sm, m):
    """Lower a narrow fixed-unpacked declaration to independent cells.

    This is the declaration half of `_fixed_array_cell`.  Only a single,
    constant-range unpacked dimension with an integral scalar/packed element
    is admitted; exact pure assignment patterns initialize its cells. The
    existing vector state then gives each cell the ordinary 4-state/2-state initialization rules.
    """
    try:
        array_type = m.type.canonicalType
        if type(array_type).__name__ != "FixedSizeUnpackedArrayType":
            return None
        dimensions_shape = _fixed_array_dimensions(array_type)
        if dimensions_shape is None:
            return None
        dimensions, leaf_type = dimensions_shape
        if type(leaf_type).__name__ == "UnpackedStructType":
            # Compose the existing shallow-struct field cells with the
            # fixed-array cell expansion.  Whole struct values and aggregate
            # array initializers still need an aggregate store, so this slice
            # admits declarations without an initializer only.
            if getattr(leaf_type, "isTagged", False) or getattr(m, "initializer", None) is not None:
                return None
            fields = list(leaf_type)
            if not fields:
                return None
            field_shapes = []
            for field in fields:
                width, two, reason = type_width_2s(field.type)
                if width is None or reason is not None:
                    return None
                if type(field.type.canonicalType).__name__ in (
                        "FixedSizeUnpackedArrayType", "DynamicArrayType",
                        "QueueType", "AssociativeArrayType",
                        "UnpackedStructType", "UnpackedUnionType"):
                    return None
                field_shapes.append((field, width, two))
            positions = [()]
            for left, right in dimensions:
                step = 1 if right >= left else -1
                positions = [prefix + (position,)
                             for prefix in positions
                             for position in range(left, right + step, step)]
            base = _array_storage_name(m)
            declarations = []
            for indexes in positions:
                cell = base + "".join(f"[{position}]" for position in indexes)
                for field, width, two in field_shapes:
                    init = ({"kind": "Literal", "span": None,
                             "width": width, "bits": "0" * width}
                            if two else None)
                    declarations.append(signed_metadata({
                        "kind": "Var", "span": sym_span(sm, m),
                        "name": f"{cell}.{field.name}",
                        "width": width, "init": init,
                    }, field.type))
            return declarations
        if len(dimensions) > 1:
            width, two, reason = type_width_2s(leaf_type)
            if width is None or reason is not None:
                return None
            initializer = getattr(m, "initializer", None)
            values = None
            if initializer is not None:
                elements = _fixed_array_pattern_elements(initializer, dimensions)
                if elements is None:
                    return None
                values = []
                target_name = _array_storage_name(m)
                for element in elements:
                    if not _case_source_expression_ok(element, packed_members=True):
                        return None
                    reads_target = False

                    def inspect(node):
                        nonlocal reads_target
                        if type(node).__name__ in ("NamedValueExpression",
                                                     "HierarchicalValueExpression"):
                            try:
                                reads_target = (reads_target or
                                                _array_storage_name(node.symbol) == target_name)
                            except Exception:
                                reads_target = True

                    _visit_selected_expression(element, inspect)
                    if reads_target:
                        return None
                    value = convert_expr(sm, element)
                    if (value is None or value.get("kind") == "Unsupported"
                            or width_of(value) != width
                            or not _case_expression_ok(value)):
                        return None
                    values.append(squash2_wrap(value, width) if two else value)
            positions = [()]
            for left, right in dimensions:
                step = 1 if right >= left else -1
                positions = [prefix + (position,)
                             for prefix in positions
                             for position in range(left, right + step, step)]
            declarations = []
            base = _array_storage_name(m)
            for index, indexes in enumerate(positions):
                init = values[index] if values is not None else None
                if init is None and two:
                    init = {"kind": "Literal", "span": None,
                            "width": width, "bits": "0" * width}
                name = base + "".join(f"[{position}]" for position in indexes)
                declarations.append(signed_metadata({
                    "kind": "Var", "span": sym_span(sm, m),
                    "name": name, "width": width, "init": init,
                }, leaf_type))
            return declarations
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
        values = _fixed_array_initializer_values(
            sm, initializer, _array_storage_name(m), width, count)
        if values is None:
            return None
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
                "name": f"{_array_storage_name(m)}[{position}]",
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
        "name": _storage_name(m),
        "width": w,
        "init": convert_expr(sm, init) if init is not None else None,
    }, m.type)


# ---------------------------------------------------------------------------
# Modules / design
# ---------------------------------------------------------------------------

def _procedural_variables(members):
    """Census declarations even inside an unentered or unsupported body."""
    symbols = set()

    def collect(node):
        if (str(getattr(node, "kind", "")) == "SymbolKind.Variable"
                and node.parentScope.isProceduralContext):
            symbols.add(node)

    for member, _route in members:
        if (not isinstance(member, dict) and str(member.kind) in (
                "SymbolKind.ProceduralBlock", "SymbolKind.StatementBlock")):
            member.visit(collect)
    return sorted(symbols, key=lambda symbol: (
        _storage_name(symbol), symbol.location.buffer.id, symbol.location.offset))


def _automatic_default_gap(symbol):
    if str(symbol.lifetime) != "VariableLifetime.Automatic":
        return False
    owner = symbol.parentScope.containingInstance
    declaration = getattr(getattr(symbol, "syntax", None), "parent", None)
    return (owner is not None
            and str(owner.definition.defaultLifetime) == "VariableLifetime.Automatic"
            and str(getattr(declaration, "kind", "")) == "SyntaxKind.DataDeclaration"
            and not any(str(token.kind) in ("TokenKind.AutomaticKeyword", "TokenKind.StaticKeyword")
                        for token in declaration.modifiers))


def _static_initializer_closed(expression, declarations):
    if expression is not None and not _case_source_expression_ok(expression, packed_members=True):
        return False
    return all(not _converted_ident_names(node.get("init"))
               and not _node_marker(node.get("init"), "plusargs_lowered")
               and _case_expression_ok(node) for node in declarations)


def _convert_static_procedural_storage(sm, members):
    symbols = _procedural_variables(members)
    _ELAB_HIER_VALUES.update(symbol for symbol in symbols
                            if str(symbol.lifetime) == "VariableLifetime.Static")
    declarations = []
    for symbol in symbols:
        if _automatic_default_gap(symbol):
            declarations.append(unsupported(sm, symbol, "AutomaticLocal:default-lifetime",
                                            "implicit procedural lifetime in an automatic module is not qualified"))
            continue
        if str(symbol.lifetime) != "VariableLifetime.Static":
            continue
        converted = convert_var(sm, symbol)
        values = converted if isinstance(converted, list) else [converted]
        if (all(value.get("kind") == "Var" for value in values)
                and not _static_initializer_closed(symbol.initializer, values)):
            values = [unsupported(sm, symbol, "StaticLocal:initializer",
                                  "static initialization needs closed pure values; ordering/effects are unmodelled")]
        for value in values:
            value["static_local_storage"] = True
            declarations.append(value)
    return declarations


def _static_initialization_barriers(sm, declarations, ports):
    names = {node["name"] for node in declarations
             if node.get("static_local_storage") and node.get("kind") == "Var"}
    return [unsupported(sm, None, "StaticLocal:initializer-order",
                        "a pre-process initializer reads procedural static storage")
            for node in declarations + ports
            if _converted_ident_names(node.get("init")) & names]


def _generated_storage_collision(ports, decls, processes, prefix):
    names = [node["name"] for node in ports + decls
             if node.get("kind") in ("Port", "Var", "Net")]

    def collect(node):
        if isinstance(node, dict):
            if node.get("kind") == "LocalDecl":
                names.append(node["name"])
            for value in node.values():
                collect(value)
        elif isinstance(node, list):
            for value in node:
                collect(value)

    collect(processes)
    generated = [name for name in names if name.startswith(prefix)]
    return any(names.count(name) != 1 for name in generated)


def _hierarchy_instance_members(sm, instance, route, context, depth):
    """Traverse the concrete body, never the frontend's shared canonical body."""
    context["instances"] += 1
    if context["instances"] > 1024 or depth > 64:
        yield unsupported(sm, instance, "Hierarchy:instance-limit"), route
        return
    # Primitive instances are concrete driver symbols, not module instances.
    # They do not expose ``isModule``; classify them as the existing loud
    # primitive boundary instead of leaking an extractor AttributeError while
    # expanding a primitive instance array.
    instance_kind = str(getattr(instance, "kind", "")).split(".")[-1]
    if instance_kind == "PrimitiveInstance":
        yield unsupported(sm, instance, "PrimitiveInstanceSymbol:PrimitiveInstance"), route
        return
    if not getattr(instance, "isModule", False):
        yield unsupported(sm, instance, "Hierarchy:module-kind"), route
        return
    body = instance.body
    if any(str(member.kind) in ("SymbolKind.Port", "SymbolKind.MultiPort") for member in body):
        yield unsupported(sm, instance, "Hierarchy:ports"), route
        return
    if str(body.definition.timeScale) != context["timescale"]:
        yield unsupported(sm, instance, "Hierarchy:timescale"), route
        return
    yield from _elaborated_members(sm, body, route, context, depth)


def _hierarchy_array_members(sm, array, route, context, depth):
    elements = list(array.elements)
    if not elements:
        yield unsupported(sm, array, "Hierarchy:invalid-array"), route
        return
    if depth > 64 or len(elements) > 1024:
        yield unsupported(sm, array, "Hierarchy:instance-limit"), route
        return
    for ordinal, element in enumerate(elements):
        path = (*route, str(ordinal))
        if str(element.kind) == "SymbolKind.InstanceArray":
            yield from _hierarchy_array_members(sm, element, path, context, depth + 1)
        else:
            yield from _hierarchy_instance_members(sm, element, path, context, depth + 1)
        if context["instances"] > 1024:
            break


def _elaborated_members(sm, scope, route=(), context=None, depth=0):
    """Flatten only live elaborated scopes; keep every active member wall."""
    for ordinal, member in enumerate(scope):
        kind = str(member.kind).split(".")[-1]
        if kind == "GenerateBlock":
            if not member.isUninstantiated:
                path = (*route, str(ordinal), member.name)
                yield from _elaborated_members(sm, member, path, context, depth)
        elif kind == "GenerateBlockArray":
            if member.isUninstantiated:
                continue
            entries = list(member.entries)
            if not member.valid or len(entries) > 1024:
                reason = "instance-limit" if len(entries) > 1024 else "invalid-array"
                yield unsupported(sm, member, "Generate:" + reason), route
            else:
                for entry in entries:
                    path = (*route, str(ordinal), member.name, str(entry.arrayIndex))
                    yield from _elaborated_members(sm, entry, path, context, depth)
        elif context is not None and kind in ("Instance", "InstanceArray"):
            context["seen"] = True
            path = ("$hierarchy", *route, str(ordinal), member.name)
            if kind == "Instance":
                yield from _hierarchy_instance_members(sm, member, path, context, depth + 1)
            else:
                yield from _hierarchy_array_members(sm, member, path, context, depth + 1)
        else:
            yield member, route


def _scope_key(route):
    return ":".join(f"{len(part)}:{part}" for part in route)


def _register_lexical_collisions(members, module_name):
    """Keep distinct bound declarations distinct after scope flattening.

    In particular an expanded let reads its declaration's binding even when
    the invocation is inside a block with a same-spelled local variable.
    Preserve public module names; rename only colliding procedural stores.
    """
    symbols = set()
    roots = {member for member, route in members if not route
             and not isinstance(member, dict)
             and str(member.kind) in ("SymbolKind.Variable", "SymbolKind.Net")}

    def collect(node):
        if str(getattr(node, "kind", "")) in ("SymbolKind.Variable", "SymbolKind.Net"):
            symbols.add(node)

    for member, route in members:
        if not route and not isinstance(member, dict):
            member.visit(collect)
    groups = {}
    for symbol in symbols:
        groups.setdefault(symbol.name, set()).add(symbol)
    # Buffer ids are process-global, so emit their compilation-local ordinal.
    buffers = {buffer: ordinal for ordinal, buffer in enumerate(
        sorted({symbol.location.buffer.id for symbol in symbols}))}
    for group in groups.values():
        if len(group) < 2:
            continue
        for symbol in group - roots:
            location = symbol.location
            _ELAB_BINDINGS[symbol] = (
                f"$local:{_scope_key((module_name,))}:{buffers[location.buffer.id]}:"
                f"{location.offset}:{symbol.name}")


def _register_elaborated_bindings(members, module_name):
    """Allocate by declaration identity, including repeated procedural locals."""
    _register_lexical_collisions(members, module_name)
    for member, route in members:
        if isinstance(member, dict):
            continue
        kind = str(member.kind).split(".")[-1]
        if kind == "Parameter":
            _ELAB_PARAMETERS.add(member)
        if kind in ("Variable", "Net"):
            _ELAB_HIER_VALUES.add(member)
        if kind == "Port":
            backing = getattr(member, "internalSymbol", None)
            if backing is not None:
                _ELAB_HIER_VALUES.add(backing)
        if not route or kind not in ("Variable", "Net", "ProceduralBlock", "StatementBlock"):
            continue
        family = "$hierarchy:" if route[0] == "$hierarchy" else "$generate:"
        prefix = family + _scope_key((module_name, *route))

        def register(node):
            if str(getattr(node, "kind", "")) in ("SymbolKind.Variable", "SymbolKind.Net"):
                _ELAB_BINDINGS[node] = f"{prefix}:{node.location.offset}:{node.name}"

        member.visit(register)


def _module_storage_collisions(ports, decls, processes, span):
    others = []
    if _generated_storage_collision(ports, decls, processes, "$intra:"):
        others.append({"kind": "Unsupported", "span": span,
                       "sv_kind": "IntraAssignment:storage-collision",
                       "text": "generated captured-value storage collides with a binding"})
    if _generated_storage_collision(ports, decls, processes, "$compound:"):
        others.append({"kind": "Unsupported", "span": span,
                       "sv_kind": "AssignmentExpression:compound-storage-collision",
                       "text": "generated operator-assignment storage collides with a binding"})
    if _generated_storage_collision(ports, decls, processes, "$plusargs:"):
        others.append({"kind": "Unsupported", "span": span,
                       "sv_kind": "Plusargs:storage-collision",
                       "text": "generated input-query storage collides with a binding"})
    if _generated_storage_collision(ports, decls, processes, "$local_array:"):
        others.append({"kind": "Unsupported", "span": span,
                       "sv_kind": "VariableDeclStatement:array-storage-collision",
                       "text": "generated local array storage collides with a binding"})
    if _generated_storage_collision(ports, decls, processes, "$foreach:"):
        others.append({"kind": "Unsupported", "span": span,
                       "sv_kind": "ForeachLoopStatement:storage-collision",
                       "text": "generated iterator storage collides with a binding"})
    if _generated_storage_collision(ports, decls, processes, "$generate:"):
        others.append({"kind": "Unsupported", "span": span,
                       "sv_kind": "Generate:storage-collision",
                       "text": "generated scope storage collides with a source binding"})
    if _generated_storage_collision(ports, decls, processes, "$hierarchy:"):
        others.append({"kind": "Unsupported", "span": span,
                       "sv_kind": "Hierarchy:storage-collision",
                       "text": "instance storage collides with a source binding"})

    if _generated_storage_collision(ports, decls, processes, "$cast:"):
        others.append({"kind": "Unsupported", "span": span,
                       "sv_kind": "DynamicCast:storage-collision",
                       "text": "generated cast storage collides with a binding"})
    if _generated_storage_collision(ports, decls, processes, "$local:"):
        others.append({"kind": "Unsupported", "span": span,
                       "sv_kind": "LexicalBinding:storage-collision",
                       "text": "lexical storage collides with a source binding"})
    return others


def convert_module(sm, inst):
    if not getattr(inst, "isModule", False):
        kind = str(getattr(inst, "kind", "")).split(".")[-1]
        marker = ("PrimitiveInstanceSymbol:PrimitiveInstance"
                  if kind == "PrimitiveInstance" else "Hierarchy:module-kind")
        return {"kind": "Module", "name": getattr(inst, "name", ""),
                "span": sym_span(sm, inst),
                "ports": [], "decls": [], "processes": [], "others": [
                    unsupported(sm, inst, marker,
                                "program/interface scheduling requires its own runtime contract"
                                if marker == "Hierarchy:module-kind" else None)]}
    body = inst.body
    span = sym_span(sm, body) or sym_span(sm, inst)
    hierarchy = {"instances": 0, "seen": False, "timescale": str(body.definition.timeScale)}
    members = list(_elaborated_members(sm, body, context=hierarchy))
    _register_elaborated_bindings(members, inst.name)
    elaborated = any(str(m.kind) in (
        "SymbolKind.GenerateBlock", "SymbolKind.GenerateBlockArray",
        "SymbolKind.Parameter", "SymbolKind.Genvar") for m in body)

    port_names = set()
    for m in body:
        if str(m.kind) == "SymbolKind.Port":
            port_names.add(m.name)

    ports = []
    decls = _convert_static_procedural_storage(sm, members)
    processes = []
    others = []
    global _ELAB_CURRENT_SCOPE
    for m, route in members:
        if isinstance(m, dict):
            others.append(m)
            continue
        _ELAB_CURRENT_SCOPE = _scope_key((inst.name, *route)) if route else ""
        previous_sizes = len(decls), len(processes)
        try:
            k = str(m.kind).split(".")[-1]
            if k == "Port":
                ports.append(convert_port(sm, m))
            elif k in ("Variable", "Net"):
                # Skip the internal symbol backing an ANSI port (same name).
                if not route and m.name in port_names:
                    continue
                if k == "Variable":
                    converted = convert_var(sm, m)
                    declarations = converted if isinstance(converted, list) else [converted]
                    for declaration in declarations:
                        reads = _converted_ident_names(declaration.get("init"))
                        if reads and (route or any(name.startswith(("$generate:", "$hierarchy:"))
                                                 for name in reads)):
                            decls.append(unsupported(sm, m, "Generate:initializer-order"))
                        else:
                            decls.append(declaration)
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
            elif _declaration_only(m) or k == "Genvar":
                continue
            elif k == "Parameter":
                width, _, reason = type_width_2s(m.type)
                value = m.value.value
                if reason is not None or type(value).__name__ != "SVInt" or value.bitWidth != width:
                    others.append(unsupported(sm, m, "Parameter:integral-value"))
            elif k in ("ExplicitImport", "WildcardImport") and m.package in _PACKAGE_SCOPES:
                # Binding is already resolved by the frontend. References keep
                # the original symbol; importing does not allocate new storage.
                continue
            else:
                others.append(unsupported(sm, m, type(m).__name__ + ":" + k))
        except Exception as exc:
            others.append(internal_error(exc))
        finally:
            if route:
                for node in decls[previous_sizes[0]:] + processes[previous_sizes[1]:]:
                    key = "instance_scope" if route[0] == "$hierarchy" else "generated_scope"
                    node[key] = list(route)
            _ELAB_CURRENT_SCOPE = ""

    processes = _lower_stateful_processes(processes)
    decls = _lower_stateful_processes(decls)
    others.extend(_module_storage_collisions(ports, decls, processes, span))
    others.extend(_static_initialization_barriers(sm, decls, ports))

    # Constant continuous windows are storage-only in the legacy runner too;
    # reject static overlap before it could be mistaken for net resolution.
    _reject_overlapping_symbolic_drivers(processes)

    module = {
        "kind": "Module",
        "span": span,
        "name": inst.name,
        "ports": ports,
        "decls": decls,
        "processes": processes,
        "others": others,
    }
    if elaborated:
        module["elaboration_lowered"] = True
    if hierarchy["seen"]:
        module["hierarchy_lowered"] = True
    return module


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
        return node.get("kind") in ("For", "Repeat", "While", "DoWhile", "Forever", "Break", "Continue") or any(
            contains_loop(value) for value in node.values())
    if isinstance(node, list):
        return any(contains_loop(value) for value in node)
    return False


def _node_marker(node, marker):
    if isinstance(node, dict):
        return node.get(marker, False) or any(_node_marker(value, marker) for value in node.values())
    if isinstance(node, list):
        return any(_node_marker(value, marker) for value in node)
    return False


def _reject_invalid_lowering(sm, comp, modules, others, marker, kind, description):
    if (_node_marker(modules, marker)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, kind + ":invalid-compilation",
                                  "frontend rejected source containing " + description))


def _closed_package_initializer(expression):
    """No runtime reads or calls may cross the static initialization boundary."""
    if expression is None:
        return True
    if not _case_source_expression_ok(expression, packed_members=True):
        return False
    closed = True

    def inspect(node):
        nonlocal closed
        if type(node).__name__ == "CallExpression":
            closed = False
        if type(node).__name__ in ("NamedValueExpression", "HierarchicalValueExpression"):
            closed = closed and str(node.symbol.kind) in (
                "SymbolKind.Parameter", "SymbolKind.EnumValue")

    _visit_selected_expression(expression, inspect)
    return closed


def _declaration_only(member):
    """Frontend-bound declarations that allocate no runtime value."""
    return (str(member.kind) == "SymbolKind.LetDecl"
            or is_integral_type_alias(member)
            or is_flat_unpacked_struct_alias(member)
            or is_bound_enum_member(member))


def _let_compilation_barriers(sm, comp):
    """Expansion must not hide an invalid or recursively defined template."""
    declarations, scopes = [], []

    def inspect(node):
        if str(getattr(node, "kind", "")) == "SymbolKind.LetDecl":
            declarations.append(node)
        if isinstance(node, Scope) and getattr(node, "syntax", None) is not None:
            scopes.append(node)

    comp.getRoot().visit(inspect)
    barriers = _bound_lowering_compilation_barriers(
        sm, comp, [{"let_expanded": bool(declarations)}], "let_expanded", "Let",
        "frontend rejected a design containing a let declaration")
    if declarations and not barriers:
        barriers.extend(_let_order_barriers(sm, comp, scopes))
    return barriers


def _let_use_scope(sm, scopes, syntax):
    """Find the innermost actual bound scope containing an original name."""
    point = sm.getFullyExpandedLoc(syntax.sourceRange.start)
    candidates = []
    for scope in scopes:
        extent = scope.syntax.sourceRange
        start, end = sm.getFullyExpandedLoc(extent.start), sm.getFullyExpandedLoc(extent.end)
        # SourceManager carries include / macro order; raw buffer offsets do not.
        after_start = point == start or sm.isBeforeInCompilationUnit(start, point)
        before_end = point == end or sm.isBeforeInCompilationUnit(point, end)
        if after_start and before_end:
            candidates.append(scope)
    # Scope visitation is preorder, so a containing descendant comes last.
    return candidates[-1] if candidates else None


def _let_order_barriers(sm, comp, scopes):
    """The frontend expands forward uses too; IEEE 11.12 forbids them."""
    barriers = []
    name_kinds = ("SyntaxKind.IdentifierName", "SyntaxKind.ScopedName",
                  "SyntaxKind.HierarchicalName")

    def inspect(syntax):
        if str(getattr(syntax, "kind", "")) not in name_kinds:
            return
        if str(getattr(syntax.parent, "kind", "")) in name_kinds:
            return
        scope = _let_use_scope(sm, scopes, syntax)
        if scope is None:
            return
        symbol = scope.lookupName(str(syntax).strip(), flags=(
            LookupFlags.AllowDeclaredAfter | LookupFlags.NoUndeclaredError))
        if symbol is None or str(symbol.kind) != "SymbolKind.LetDecl":
            return
        if sm.isBeforeInCompilationUnit(sm.getFullyExpandedLoc(syntax.sourceRange.start),
                                        sm.getFullyExpandedLoc(symbol.location)):
            barriers.append(unsupported(sm, syntax, "Let:used-before-declaration",
                                        "let must be declared before use in its lexical scope"))

    for tree in comp.getSyntaxTrees():
        tree.root.visit(inspect)
    return barriers


def _convert_package(sm, package):
    """Compile a package's integral static store, preserving all other walls."""
    decls, others = [], []
    for member in package:
        kind = str(member.kind).split(".")[-1]
        if kind in ("ExplicitImport", "WildcardImport") and member.package in _PACKAGE_SCOPES:
            continue
        if _declaration_only(member):
            continue
        if kind == "Parameter":
            width, _, reason = type_width_2s(member.type)
            value = member.value.value
            if reason is None and type(value).__name__ == "SVInt" and value.bitWidth == width:
                continue
        if kind == "Variable":
            width, _, reason = type_width_2s(member.type)
            if reason is not None or width is None:
                others.append(unsupported(sm, member, "Package:storage-type"))
                continue
            if not _closed_package_initializer(member.initializer):
                others.append(unsupported(sm, member, "Package:initializer"))
                continue
            declaration = convert_var(sm, member)
            declaration.update(package_storage=True, source_package=package.name,
                               source_name=member.name)
            decls.append(declaration)
        else:
            others.append(unsupported(sm, member, "Package:" + kind))
    return decls, others


def _package_import_sets(package, active=()):
    """Return in-scope / exported declarations by original symbol identity.

    The frontend exposes unexported explicit imports to subsequent imports.
    Reconstruct the IEEE export filter rather than trusting that exposure.
    A cycle is outside this admission check, never permission to invent names.
    """
    if package in active:
        return set(), set()
    members = list(package)
    imports = [m for m in members if str(m.kind) in (
        "SymbolKind.ExplicitImport", "SymbolKind.WildcardImport") and not m.isFromExport]
    exports = [m for m in members if str(m.kind) in (
        "SymbolKind.ExplicitImport", "SymbolKind.WildcardImport") and m.isFromExport]
    own = {getattr(m, "wrapped", m) for m in members if str(m.kind) not in (
        "SymbolKind.ExplicitImport", "SymbolKind.WildcardImport")}
    in_scope, visible = set(own), set(own)
    for binding in imports:
        source = binding.package
        if source not in _PACKAGE_SCOPES:
            continue
        _, candidates = _package_import_sets(source, (*active, package))
        if str(binding.kind) == "SymbolKind.ExplicitImport":
            candidates &= {binding.importedSymbol}
        in_scope.update(candidates)
        for symbol in candidates:
            if package.hasExportAll or any(
                    export.package == source and (
                        str(export.kind) == "SymbolKind.WildcardImport"
                        or export.importedSymbol == symbol) for export in exports):
                visible.add(symbol)
    return in_scope, visible


def _invalid_package_imports(comp):
    """Audit the frontend's importable names against the IEEE export filter."""
    invalid = False

    def inspect(member):
        nonlocal invalid
        kind = str(getattr(member, "kind", ""))
        if kind not in ("SymbolKind.ExplicitImport", "SymbolKind.WildcardImport"):
            return
        source = member.package
        if source not in _PACKAGE_SCOPES:
            return
        in_scope, visible = _package_import_sets(source)
        if kind == "SymbolKind.ExplicitImport":
            invalid = invalid or member.importedSymbol not in visible
        else:
            # Unreferenced wildcard candidates are not declarations imported
            # into the relay. Reject only hidden names the frontend actually
            # exposes for import, without admitting them as exported bindings.
            invalid = invalid or any(source.findForImport(symbol.name) == symbol
                                     for symbol in in_scope - visible)

    comp.getRoot().visit(inspect)
    return invalid


def convert_design(sm, comp):
    # Keep the binding environment local to this extraction, including on an
    # error path. Symbol objects identify declarations without parsing paths
    # (escaped identifiers themselves may contain :: or punctuation).
    global _PACKAGE_BINDINGS, _PACKAGE_SCOPES, _MIN_TYP_MAX
    global _ELAB_BINDINGS, _ELAB_PARAMETERS, _ELAB_HIER_VALUES, _ELAB_CURRENT_SCOPE
    previous = (_PACKAGE_BINDINGS, _PACKAGE_SCOPES, _ELAB_BINDINGS,
                _ELAB_PARAMETERS, _ELAB_HIER_VALUES, _ELAB_CURRENT_SCOPE, _MIN_TYP_MAX)
    _MIN_TYP_MAX = {MinTypMax.Min: "min", MinTypMax.Typ: "typ", MinTypMax.Max: "max"}[
        comp.options.minTypMax]
    _ELAB_BINDINGS, _ELAB_PARAMETERS, _ELAB_HIER_VALUES, _ELAB_CURRENT_SCOPE = {}, set(), set(), ""
    packages = [member for unit in comp.getCompilationUnits() for member in unit
                if str(member.kind) == "SymbolKind.Package"]
    _PACKAGE_SCOPES = set(packages)
    _PACKAGE_BINDINGS = {
        member: f"$package:{len(package.name)}:{package.name}:{member.name}"
        for package in packages for member in package
        if str(member.kind) in ("SymbolKind.Variable", "SymbolKind.Parameter")}
    try:
        return _convert_design(sm, comp, packages)
    finally:
        (_PACKAGE_BINDINGS, _PACKAGE_SCOPES, _ELAB_BINDINGS,
         _ELAB_PARAMETERS, _ELAB_HIER_VALUES, _ELAB_CURRENT_SCOPE, _MIN_TYP_MAX) = previous


def _selected_compilation_barriers(sm, comp):
    """Keep selected expression lowering behind whole-source validity."""
    if _SYM is not None or not any(
            diagnostic.isError() or str(diagnostic.code) in (
                "DiagCode(Redefinition)", "DiagCode(RedefinitionDifferentType)")
            for diagnostic in comp.getAllDiagnostics()):
        return []
    barriers = []
    for predicate, category, detail in (
            (_has_min_typ_max, "MinTypMaxExpression:invalid-compilation",
             "frontend rejected a design containing min/typ/max selection"),
            (_has_compound_assignment, "AssignmentExpression:compound-invalid-compilation",
             "frontend rejected a design containing an operator assignment")):
        if predicate(comp):
            barriers.append(unsupported(sm, comp, category, detail))
    return barriers


def _bound_lowering_compilation_barriers(sm, comp, modules, marker, family, description):
    if not any(_node_marker(module, marker) for module in modules):
        return []
    if any(diagnostic.isError() or str(diagnostic.code) in (
            "DiagCode(Redefinition)", "DiagCode(RedefinitionDifferentType)")
           for diagnostic in comp.getAllDiagnostics()):
        return [unsupported(sm, comp, family + ":invalid-compilation", description)]
    return []


def _convert_design(sm, comp, packages):
    modules = []
    others = []
    package_decls = []
    for package in packages:
        try:
            declarations, walls = _convert_package(sm, package)
            package_decls.extend(declarations)
            others.extend(walls)
        except Exception as exc:
            others.append(internal_error(exc))
    for inst in comp.getRoot().topInstances:
        try:
            modules.append(convert_module(sm, inst))
        except Exception as exc:
            modules.append(internal_error(exc))
    if package_decls:
        if len(modules) == 1 and modules[0].get("kind") == "Module":
            module = modules[0]
            module["decls"] = package_decls + module["decls"]
            if _generated_storage_collision(module["ports"], module["decls"],
                                            module["processes"], "$package:"):
                others.append(unsupported(sm, comp, "Package:storage-collision",
                                          "package storage collides with a source binding"))
        else:
            others.append(unsupported(sm, comp, "Package:multiple-modules",
                                      "shared package storage requires the single-module runner"))
    if packages and _invalid_package_imports(comp):
        others.append(unsupported(sm, comp, "Package:import-visibility",
                                  "import exposes an unexported package binding or candidate"))
    if packages and any(diagnostic.isError() or str(diagnostic.code) == "DiagCode(Redefinition)"
                        for diagnostic in comp.getAllDiagnostics()):
        others.append(unsupported(sm, comp, "Package:invalid-compilation",
                                  "frontend rejected source containing a package"))
    # Unit variables and other runtime $unit-scope members remain outside M0.
    try:
        for unit in comp.getCompilationUnits():
            for m in unit:
                if str(m.kind) == "SymbolKind.Package":
                    continue
                if (str(m.kind) in ("SymbolKind.ExplicitImport", "SymbolKind.WildcardImport")
                        and m.package in _PACKAGE_SCOPES):
                    continue
                if _declaration_only(m):
                    continue
                others.append(unsupported(sm, m, type(m).__name__))
    except Exception as exc:
        others.append(internal_error(exc))
    if (any(_node_marker(module, "elaboration_lowered") for module in modules)
            and any(diagnostic.isError() or str(diagnostic.code) == "DiagCode(Redefinition)"
                    for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "Elaboration:invalid-compilation",
                                  "frontend rejected an elaborated scope or parameter design"))
    if (any(_node_marker(module, "assignment_pattern_lowered") for module in modules)
            and any(diagnostic.isError() or str(diagnostic.code) in (
                        "DiagCode(Redefinition)", "DiagCode(RedefinitionDifferentType)")
                    for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "AssignmentPattern:invalid-compilation",
                                  "frontend rejected a design containing an assignment pattern"))
    if (any(_node_marker(module, "replication_lowered") for module in modules)
            and any(diagnostic.isError() or str(diagnostic.code) in (
                        "DiagCode(Redefinition)", "DiagCode(RedefinitionDifferentType)")
                    for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "Replication:invalid-compilation",
                                  "frontend rejected a design containing a replication"))
    if _unsized_based_constant_gap(comp):
        others.append(unsupported(sm, comp, "UnsizedBasedLiteral:constant-context",
                                  "frontend widening of an unsized X/Z elaboration constant"))
    if _SYM is None and _constant_context_gap(comp, _contains_unresolved_clog2):
        others.append(unsupported(sm, comp, "$clog2:constant-context",
                                  "unresolved or unknown clog2 elaboration argument"))
    others.extend(_selected_compilation_barriers(sm, comp))
    others.extend(_bound_lowering_compilation_barriers(
        sm, comp, modules, "hierarchy_lowered", "Hierarchy",
        "frontend rejected an elaborated module hierarchy"))
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
    _reject_invalid_lowering(sm, comp, modules, others, "always_lowered",
                             "Always", "a repeating procedural process")
    _reject_invalid_lowering(sm, comp, modules, others, "assertion_lowered",
                             "ImmediateAssertion", "a lowered immediate assertion")
    if (any(contains_fixed_bits_query(module) for module in modules)
            and any(diagnostic.isError() for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "$bits:invalid-compilation",
                                  "frontend rejected source containing a fixed-size query"))
    if (any(contains_fixed_clog2(module) or _node_marker(module, "runtime_clog2")
            for module in modules)
            and any(diagnostic.isError() or str(diagnostic.code) in (
                        "DiagCode(Redefinition)", "DiagCode(RedefinitionDifferentType)")
                    for diagnostic in comp.getAllDiagnostics())):
        others.append(unsupported(sm, comp, "$clog2:invalid-compilation",
                                  "frontend rejected source containing a clog2 call"))
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
    _reject_invalid_lowering(sm, comp, modules, others, "inside_lowered",
                             "InsideExpression", "lowered membership")
    _reject_invalid_lowering(sm, comp, modules, others, "implication_lowered",
                             "LogicalImplication", "lowered implication")
    _reject_invalid_lowering(sm, comp, modules, others, "intra_assignment_lowered",
                             "IntraAssignment", "intra-assignment timing")
    _reject_invalid_lowering(sm, comp, modules, others, "plusargs_lowered",
                             "Plusargs", "command-line input query")
    _reject_invalid_lowering(sm, comp, modules, others, "scanf_lowered",
                             "Scanf", "formatted input")
    _reject_invalid_lowering(sm, comp, modules, others, "enum_method_lowered",
                             "EnumMethod", "numeric enum method")
    others.extend(_bound_lowering_compilation_barriers(
        sm, comp, modules, "dynamic_cast_lowered", "DynamicCast",
        "frontend rejected a dynamic integral cast"))
    others.extend(_bound_lowering_compilation_barriers(
        sm, comp, modules, "array_reduction_lowered", "ArrayReduction",
        "frontend rejected a fixed-array reduction"))
    others.extend(_let_compilation_barriers(sm, comp))
    others.extend(_bound_lowering_compilation_barriers(
        sm, comp, modules, "static_local_storage", "StaticLocal",
        "frontend rejected a design containing procedural static storage"))
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
        if cname in ("PackedStructType", "PackedUnionType"):
            if getattr(ct, "isTagged", False):
                return None, "tagged-struct"
            # The semantic tier stores an untagged packed struct/union as one
            # fixed vector; member offsets become PartSel windows below.
            width = int(ct.bitWidth)
            if width <= 0:
                return None, "type"
            return {
                "kind": "PackedType",
                "packed": [{
                    "msb": {"kind": "Int", "span": None,
                            "value": width - 1, "resolved_width": None},
                    "lsb": {"kind": "Int", "span": None,
                            "value": 0, "resolved_width": None},
                }],
                "resolved": width,
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
    array_decls = convert_fixed_array_vars_sym(sm, m)
    if array_decls is not None:
        return array_decls
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


def convert_fixed_array_vars_sym(sm, m):
    """Lower a fixed one-dimensional unpacked integral array to cells.

    The semantic tier has a flat vector store, so each constant-index cell is
    represented by its own declaration name (the same representation used by
    ``_fixed_array_cell``). A pure exact assignment-pattern initializer can
    populate those cells directly; nested arrays and aggregate initializers
    remain outside this narrow admission.
    """
    try:
        array_type = m.type.canonicalType
        if type(array_type).__name__ != "FixedSizeUnpackedArrayType":
            return None
        element_type = array_type.elementType
        if type(element_type.canonicalType).__name__ == "FixedSizeUnpackedArrayType":
            return None
        element_kind = type(element_type.canonicalType).__name__
        width, two, reason = type_width_2s(element_type)
        if width is None or reason is not None:
            return None
        # ``VariableSymbol.declaredType.typeSyntax`` describes the packed
        # element type even when the symbol itself has an unpacked suffix;
        # pass it through so the flattened cell remains an instantiable
        # symbolic PackedType rather than an unrecoverable null-dimension
        # placeholder.
        dtype, dtype_reason = _dtype_sym(sm, element_type, _decl_type_syntax(m))
        if (dtype is not None and dtype_reason is None
                and dtype.get("kind") == "PackedType"
                and dtype.get("packed") is None):
            # A plain packed typedef has no LogicType syntax at this use
            # site, but its canonical element type still carries fixed
            # ranges. Recover those ranges so flattened cells can pass the
            # symbolic instantiator's width checks without a nominal table.
            dims = []
            current = element_type.canonicalType
            while type(current).__name__ == "PackedArrayType":
                rng = current.range
                dims.append({
                    "msb": {"kind": "Int", "span": None,
                            "value": int(rng.left), "resolved_width": None},
                    "lsb": {"kind": "Int", "span": None,
                            "value": int(rng.right), "resolved_width": None},
                })
                current = current.elementType.canonicalType
            if type(current).__name__ != "ScalarType" or not dims:
                return None
            dtype["packed"] = dims
        if dtype is None or dtype_reason is not None:
            return None
        left, right = int(array_type.range.left), int(array_type.range.right)
        count = abs(left - right) + 1
        if count <= 0 or count > 1024:
            return None
        initializer = getattr(m, "initializer", None)
        values = [None] * count
        if initializer is not None:
            # A packed aggregate's runtime representation is a vector, but
            # its nested assignment-pattern syntax needs an aggregate-aware
            # evaluator. Keep that form loud rather than treating a pattern
            # as an arbitrary bit vector. The scalar/packed/enum cases below
            # are already represented by ordinary symbolic expressions.
            if element_kind in ("PackedStructType", "PackedUnionType"):
                return None
            pattern_kind = type(initializer).__name__
            if pattern_kind not in (
                    "SimpleAssignmentPatternExpression",
                    "StructuredAssignmentPatternExpression",
                    "ReplicatedAssignmentPatternExpression"):
                return None
            if getattr(initializer, "bad", False):
                return None
            if pattern_kind == "ReplicatedAssignmentPatternExpression":
                repetition = getattr(getattr(initializer, "count", None),
                                     "constant", None)
                try:
                    if hasattr(repetition, "value"):
                        repetition = repetition.value
                    repetition = int(repetition)
                except (TypeError, ValueError, OverflowError):
                    return None
                if repetition <= 0:
                    return None
                source_elements = _pattern_source_elements(initializer)
                if (not source_elements
                        or repetition * len(source_elements) != count):
                    return None
                elements = source_elements * repetition
            else:
                elements = _pattern_source_elements(initializer)
                if len(elements) != count:
                    return None
            for i, element in enumerate(elements):
                if not _case_source_expression_ok(element, packed_members=True):
                    return None
                value = convert_expr(sm, element)
                if (value is None or value.get("kind") == "Unsupported"
                        or width_of(value) != width
                        or not _case_expression_ok(value)):
                    return None
                reads_target = False

                def inspect(node):
                    nonlocal reads_target
                    if type(node).__name__ == "NamedValueExpression":
                        try:
                            reads_target = reads_target or node.symbol.name == m.name
                        except Exception:
                            reads_target = True

                _visit_selected_expression(element, inspect)
                if reads_target:
                    return None
                values[i] = value
        step = 1 if right >= left else -1
        decls = []
        for i, position in enumerate(range(left, right + step, step)):
            init = None
            if values[i] is not None:
                init = values[i]
            if init is None and two:
                init = {"kind": "Literal", "span": None, "width": width,
                        "bits": "0" * width}
            decls.append({
                "kind": "Var",
                "span": sym_span(sm, m),
                "name": f"{m.name}[{position}]",
                "width": dtype,
                "init": init,
            })
        return decls
    except Exception:
        return None


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
            converted = _convert_member_sym(sm, m, k)
            if isinstance(converted, list):
                out.extend(converted)
            elif converted is not None:
                out.append(converted)
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
            if is_integral_type_alias(m):
                # Plain packed integral aliases are compile-time metadata in
                # the same way as packed-struct/union aliases. Uses retain
                # their canonical dimensions at each declaration site.
                return None
            if type(m.declaredType.type.canonicalType).__name__ in (
                    "PackedStructType", "PackedUnionType"):
                # A packed-struct/union typedef is compile-time metadata only
                # in this tier; variables still lower to their fixed vector
                # width and member offsets at each use site.
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
                converted = (convert_var_sym(sm, m) if k == "Variable"
                             else convert_net_sym(sm, m))
                if isinstance(converted, list):
                    decls.extend(converted)
                else:
                    decls.append(converted)
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

    _reject_overlapping_symbolic_drivers(processes)

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
            _reject_invalid_lowering(sm, comp, [module], module["others"],
                                     "implication_lowered", "LogicalImplication",
                                     "lowered implication")
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


def _compilation_with_choice(choice):
    options = CompilationOptions()
    options.minTypMax = {"min": MinTypMax.Min, "typ": MinTypMax.Typ, "max": MinTypMax.Max}[choice]
    return Compilation(pyslang.Bag([options]))


def process_file(source_path, min_typ_max="typ"):
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
    comp = _compilation_with_choice(min_typ_max)
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
    if min_typ_max != "typ":
        envelope["min_typ_max"] = min_typ_max

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
    parser.add_argument("--min-typ-max", choices=("min", "typ", "max"), default="typ",
                        help="legacy elaboration choice for min:typ:max expressions (default: typ)")
    args = parser.parse_args(argv)

    try:
        if args.top is not None:
            if args.min_typ_max != "typ":
                raise ExtractError("--min-typ-max min/max is not admitted in symbolic mode")
            out = process_symbolic(args.top, args.sources, args.incdirs,
                                   args.out)
            print(out)
        else:
            if args.incdirs or args.out:
                raise ExtractError("-I/-o require --top (symbolic mode)")
            for src in args.sources:
                process_file(src, args.min_typ_max)
    except ExtractError as e:
        print("error: %s" % e, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
