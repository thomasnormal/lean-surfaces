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
from decimal import Decimal, InvalidOperation, ROUND_DOWN
import hashlib
import json
import math
import os
import re
import struct
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
SYSCALL_STROBE = "$strobe"
# File-format tasks are admitted only for the predefined stdout descriptor;
# `$fwrite` maps to the existing no-newline `$write` node.
SYSCALL_FILE_FMT = ("$fdisplay", "$fwrite")
SYSCALL_CTRL = ("$finish", "$stop")
SYSCALL_FATAL = "$fatal"
# `$sdf_annotate` changes simulator timing data, which is outside the
# time-zero self-check state.  The narrow inert slice below admits only
# literal filenames, optionally paired with a static module scope or an
# explicit empty config string.  Calls carrying a nonempty config or other
# optional arguments stay loud until the timing model exists.
SYSCALL_SDF = "$sdf_annotate"
SYSCALL_TIMEFORMAT = "$timeformat"
# `$printtimescale` reports scope metadata without changing modeled state.  The
# no-argument form is therefore safe to erase in the self-check tier; explicit
# scope arguments remain loud because hierarchy/time-scale semantics are not
# represented in the envelope state.  `$exit` is likewise inert for the
# module-originating initial processes admitted by this tier (§24.7); program
# process control is outside the self-check surface.
SYSCALL_PURE_DIAGNOSTIC = ("$printtimescale", "$exit")
# VCD setup tasks affect only an external waveform file, which is outside the
# self-check oracle's observable state.  Their syntax is retained by the
# frontend, while the tier erases the static setup calls below.
SYSCALL_VCD = ("$dumpfile", "$dumpvars", "$dumpon", "$dumpoff",
               "$dumpall", "$dumpflush", "$dumplimit")
# Severity tasks only affect a simulator's diagnostic stream.  The public
# self-check state has no diagnostic channel, so a pure literal call can be
# erased while preserving control flow and all modeled state.  Calls with
# evaluated arguments remain outside this slice: evaluating an argument can
# itself have observable effects.
SYSCALL_QUIET = ("$info", "$warning", "$error")
# No concurrent-assertion state exists in the self-check interpreter.  Bare
# assertion-control tasks therefore have no modeled effect; scoped or
# argumented controls remain loud until assertion state is represented.
SYSCALL_ASSERT_CTRL = ("$asserton", "$assertoff", "$assertkill", "$assertcontrol")
# Monitor toggles only affect an active `$monitor` registration.  The
# self-check state has no monitor stream, so no-argument toggles are inert when
# the design contains no registration; registered monitors stay loud.
SYSCALL_MONITOR_CTRL = ("$monitoron", "$monitoroff")
# Coverage query calls have no represented coverage database in the
# self-check state.  A literal-only call therefore has the standard
# ``SV_COV_NOCOV`` result (zero); calls that could observe registered
# coverage, external databases, or dynamic scope remain loud.
COVERAGE_CALLS = ("$coverage_control", "$coverage_get", "$coverage_get_max",
                  "$coverage_merge", "$coverage_save")
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


def _sv_code_source(source):
    """Blank comments and string literals while preserving source offsets.

    A few narrow source-order recognizers use regular expressions after the
    frontend has proved the relevant AST shape.  Their scans must not treat a
    variable name mentioned in a comment or a diagnostic format string as a
    second runtime use.  Keep every character position intact so the masked
    text can still be compared with ``SourceRange`` offsets.
    """
    chars = list(source)
    i = 0
    state = "code"
    while i < len(chars):
        if state == "code":
            if source.startswith("//", i):
                chars[i] = chars[i + 1] = " "
                i += 2
                state = "line-comment"
            elif source.startswith("/*", i):
                chars[i] = chars[i + 1] = " "
                i += 2
                state = "block-comment"
            elif source[i] == '"':
                chars[i] = " "
                i += 1
                state = "string"
            else:
                i += 1
        elif state == "line-comment":
            if source[i] == "\n":
                state = "code"
                i += 1
            else:
                chars[i] = " "
                i += 1
        elif state == "block-comment":
            if source.startswith("*/", i):
                chars[i] = chars[i + 1] = " "
                i += 2
                state = "code"
            else:
                if source[i] != "\n":
                    chars[i] = " "
                i += 1
        else:  # string
            if source[i] == "\\":
                chars[i] = " "
                i += 1
                if i < len(chars) and source[i] != "\n":
                    chars[i] = " "
                    i += 1
            elif source[i] == '"':
                chars[i] = " "
                i += 1
                state = "code"
            else:
                if source[i] != "\n":
                    chars[i] = " "
                i += 1
    return "".join(chars)

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
            # through every packed layer before checking the integral leaf;
            # the LVec state preserves the complete bit ordering, including
            # nested packed arrays and packed enum/struct leaves.
            while type(elem).__name__ == "PackedArrayType":
                elem = elem.elementType.canonicalType
            if type(elem).__name__ in ("ScalarType", "EnumType",
                                       "PackedStructType", "PackedUnionType"):
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
        return (reason is None
                or _fixed_query_dimensions(symbol.declaredType.type) is not None
                or _unpacked_union_shape(symbol.declaredType.type) is not None)
    except Exception:
        return False


def is_module_event_decl(symbol):
    """Whether a module-scope named event has no self-check observation.

    The time-zero self-check surface has no event object slot. A declaration
    can nevertheless be admitted as inert metadata when no procedural code
    uses it; event triggers and waits continue through their loud boundaries.
    """
    if str(getattr(symbol, "kind", "")) != "SymbolKind.Variable":
        return False
    try:
        return (not symbol.parentScope.isProceduralContext
                and type(symbol.type.canonicalType).__name__ == "EventType")
    except Exception:
        return False


def is_module_floating_decl(symbol):
    """Whether a module-scope real/shortreal declaration is inert metadata."""
    if str(getattr(symbol, "kind", "")) != "SymbolKind.Variable":
        return False
    try:
        return (not symbol.parentScope.isProceduralContext
                and type(symbol.type.canonicalType).__name__ == "FloatingType")
    except Exception:
        return False


def is_inert_2state_floating_decl(symbol):
    """Whether a procedural real declaration is inert.

    Real and shortreal storage has no representation in the self-check
    state. An uninitialized local, or one initialized by a pure real literal,
    has no observable effect by itself; reads remain loud at their expression
    boundary and effectful initializers remain represented as refusals.
    """
    if str(getattr(symbol, "kind", "")) != "SymbolKind.Variable":
        return False
    try:
        if (not symbol.parentScope.isProceduralContext
                or type(symbol.type.canonicalType).__name__ != "FloatingType"):
            return False
        initializer = getattr(symbol, "initializer", None)
        if initializer is None:
            return True
        if type(initializer).__name__ in ("RealLiteral", "ShortRealLiteral"):
            return True
        if type(initializer).__name__ == "ConversionExpression":
            return (type(getattr(initializer, "operand", None)).__name__
                    in ("RealLiteral", "ShortRealLiteral"))
        if type(initializer).__name__ == "UnaryExpression":
            op = str(getattr(initializer, "op", "")).split(".")[-1]
            return (op in ("Plus", "Minus", "UnaryPlus", "UnaryMinus")
                    and type(getattr(initializer, "operand", None)).__name__
                    in ("RealLiteral", "ShortRealLiteral"))
        return False
    except Exception:
        return False


def is_chandle_decl(symbol):
    """Whether a declaration names the opaque IEEE chandle type."""
    try:
        return type(symbol.type.canonicalType).__name__ == "CHandleType"
    except Exception:
        return False


def is_inert_class_handle_decl(symbol):
    """Whether an uninitialized class handle is declaration-only metadata.

    A class handle starts as null, but the flat self-check state has no object
    or handle slot.  The declaration itself has no observable effect; reads,
    writes, construction, and method calls continue through their existing
    loud boundaries.
    """
    if str(getattr(symbol, "kind", "")) != "SymbolKind.Variable":
        return False
    try:
        canonical = symbol.type.canonicalType
        if type(canonical).__name__ != "ClassType":
            return False
        initializer = getattr(symbol, "initializer", None)
        if getattr(canonical, "name", None) != "mailbox":
            return initializer is None
        # A mailbox handle has no flat storage.  The uninitialized form and
        # direct ``mailbox#(T) mbx = new()`` form are both declaration
        # metadata at either scope; the source-ordered mailbox recognizers
        # account for subsequent put/get/num calls. Other initialized class
        # handles stay on the ordinary loud boundary.
        if initializer is None:
            return True
        if type(initializer).__name__ != "NewClassExpression":
            return False
        # pyslang supplies the mailbox's implicit default size as a synthetic
        # constructor argument, so the AST argument count cannot distinguish
        # ``new()`` from an explicit bounded constructor.  Use only the
        # initializer's source spelling for this declaration-only shortcut.
        if not _SOURCE_BYTES:
            return False
        start = getattr(getattr(initializer, "sourceRange", None), "start", None)
        end = getattr(getattr(initializer, "sourceRange", None), "end", None)
        start = getattr(start, "offset", None)
        end = getattr(end, "offset", None)
        if start is None or end is None:
            return False
        spelling = _SOURCE_BYTES[start:end].decode("utf-8", errors="replace")
        return bool(re.fullmatch(r"\s*new\s*\(\s*\)\s*", spelling))
    except Exception:
        return False


def is_literal_semaphore_decl(symbol):
    """Whether a semaphore declaration has one literal constructor value.

    The self-check state has no semaphore object slot.  A direct literal
    constructor is nevertheless useful to the narrow ``try_get`` lowering
    below, which tracks the available count from the source-ordered calls.
    Other initialized class handles remain on the ordinary loud boundary.
    """
    if str(getattr(symbol, "kind", "")) != "SymbolKind.Variable":
        return False
    try:
        return (type(symbol.type.canonicalType).__name__ == "ClassType"
                and getattr(symbol.type.canonicalType, "name", None) == "semaphore"
                and _semaphore_new_nonnegative_literal(
                    getattr(symbol, "initializer", None)))
    except Exception:
        return False


def is_module_virtual_interface_null_decl(symbol):
    """Whether a module virtual-interface variable is initialized to null."""
    if str(getattr(symbol, "kind", "")) != "SymbolKind.Variable":
        return False
    try:
        if (symbol.parentScope.isProceduralContext
                or type(symbol.type.canonicalType).__name__ != "VirtualInterfaceType"):
            return False
        initializer = getattr(symbol, "initializer", None)
        if type(initializer).__name__ != "ConversionExpression":
            return False
        return type(getattr(initializer, "operand", None)).__name__ == "NullLiteral"
    except Exception:
        return False


def is_string_decl(symbol):
    """Whether an unused declaration names an opaque SystemVerilog string.

    A missing initializer or a pure string-literal initializer has no
    observable effect on the time-zero self-check path and can be omitted from
    the flat state.  Any other initializer remains a value boundary.
    """
    if str(getattr(symbol, "kind", "")) != "SymbolKind.Variable":
        return False
    try:
        if type(symbol.type.canonicalType).__name__ != "StringType":
            return False
        if (not symbol.parentScope.isProceduralContext
                and getattr(symbol.parentScope, "containingInstance", None) is None):
            return False
        initializer = getattr(symbol, "initializer", None)
        if initializer is None:
            return True
        if type(initializer).__name__ == "StringLiteral":
            return not getattr(initializer, "bad", False)
        return (type(initializer).__name__ == "ConversionExpression"
                and type(getattr(initializer, "operand", None)).__name__ == "StringLiteral"
                and not getattr(initializer, "bad", False)
                and not getattr(initializer.operand, "bad", False))
    except Exception:
        return False


def is_inert_2state_queue_decl(symbol):
    """Whether a 2-state queue declaration is only metadata.

    Queue reads, writes, methods, and aggregate values remain outside the
    self-check state.  An uninitialized queue, or one initialized by the
    empty queue pattern/concatenation, therefore has no represented value;
    nonempty and effectful initializers remain a boundary because they create
    a value that could matter.
    """
    if str(getattr(symbol, "kind", "")) != "SymbolKind.Variable":
        return False
    try:
        if (symbol.type.isFourState
                or type(symbol.type.canonicalType).__name__ != "QueueType"):
            return False
        initializer = getattr(symbol, "initializer", None)
        if initializer is None:
            return True
        kind = type(initializer).__name__
        if kind == "ConcatenationExpression":
            return not list(getattr(initializer, "operands", ()))
        if kind == "SimpleAssignmentPatternExpression":
            return not list(getattr(initializer, "elements", ()))
        return False
    except Exception:
        return False


def is_inert_2state_dynamic_array_decl(symbol):
    """Whether an uninitialized 2-state dynamic array is declaration-only."""
    if str(getattr(symbol, "kind", "")) != "SymbolKind.Variable":
        return False
    try:
        return (not symbol.type.isFourState
                and type(symbol.type.canonicalType).__name__ == "DynamicArrayType"
                and getattr(symbol, "initializer", None) is None
                and _dynamic_array_constant_extent(symbol) is None)
    except Exception:
        return False


def is_inert_2state_associative_array_decl(symbol):
    """Whether an uninitialized 2-state associative array is declaration-only."""
    if str(getattr(symbol, "kind", "")) != "SymbolKind.Variable":
        return False
    try:
        return (not symbol.type.isFourState
                and type(symbol.type.canonicalType).__name__ == "AssociativeArrayType"
                and getattr(symbol, "initializer", None) is None)
    except Exception:
        return False


def is_flat_unpacked_struct_alias(symbol):
    """Whether a typedef names an integral-only unpacked struct tree.

    Such a typedef is metadata for the legacy field-flattening path; it does
    not allocate an aggregate value by itself. Nested struct fields are
    admitted recursively; other aggregate fields remain declaration
    boundaries until they have their own representation.
    """
    if str(symbol.kind) != "SymbolKind.TypeAlias":
        return False
    try:
        aggregate = symbol.declaredType.type.canonicalType
        if type(aggregate).__name__ != "UnpackedStructType":
            return False
        if getattr(aggregate, "isTagged", False):
            return False
        def integral_tree(node, seen):
            marker = id(node)
            if marker in seen or type(node).__name__ != "UnpackedStructType":
                return False
            fields = list(node)
            if not fields:
                return False
            seen = seen | {marker}
            for field in fields:
                leaf = field.type.canonicalType
                if type(leaf).__name__ == "UnpackedStructType":
                    if not integral_tree(leaf, seen):
                        return False
                    continue
                if type(leaf).__name__ == "FixedSizeUnpackedArrayType":
                    array_shape = _fixed_array_dimensions(field.type,
                                                           max_cells=1024)
                    if array_shape is None:
                        return False
                    _dimensions, array_leaf = array_shape
                    width, _, reason = type_width_2s(array_leaf)
                    if (width is None or reason is not None or
                            type(array_leaf.canonicalType).__name__ in (
                                "FixedSizeUnpackedArrayType",
                                "DynamicArrayType", "QueueType",
                                "AssociativeArrayType", "UnpackedStructType",
                                "UnpackedUnionType")):
                        return False
                    continue
                width, _, reason = type_width_2s(field.type)
                if width is None or reason is not None:
                    return False
                if type(leaf).__name__ in (
                        "FixedSizeUnpackedArrayType", "DynamicArrayType",
                        "QueueType", "AssociativeArrayType", "UnpackedUnionType"):
                    return False
            return True
        return integral_tree(aggregate, set())
    except Exception:
        return False


def _unpacked_union_shape(type_or_declared):
    """Return the shared width/state of a shallow integral unpacked union.

    The legacy state has no aggregate object slot, but an untagged union whose
    members are all the same-width integral vector can alias one ordinary
    vector exactly: every member read/write names the same cell.  Restrict the
    helper to equal widths and equal four-state kind so no padding or dynamic
    aggregate semantics are guessed.
    """
    try:
        aggregate = getattr(type_or_declared, "canonicalType", type_or_declared)
        if type(aggregate).__name__ != "UnpackedUnionType":
            return None
        if getattr(aggregate, "isTagged", False):
            return None
        fields = list(aggregate)
        if not fields:
            return None
        widths = []
        state = None
        for field in fields:
            leaf = field.type.canonicalType
            if type(leaf).__name__ in (
                    "FixedSizeUnpackedArrayType", "DynamicArrayType",
                    "QueueType", "AssociativeArrayType", "UnpackedStructType",
                    "UnpackedUnionType"):
                return None
            width, two_state, reason = type_width_2s(field.type)
            if width is None or reason is not None:
                return None
            widths.append(width)
            current_state = bool(two_state)
            if state is None:
                state = current_state
            elif state != current_state:
                return None
        if len(set(widths)) != 1:
            return None
        return widths[0], bool(state)
    except Exception:
        return None


def _unpacked_union_decls(sm, symbol):
    """Flatten an admitted shallow unpacked union into one aliased vector."""
    try:
        shape = _unpacked_union_shape(symbol.type)
        if shape is None or getattr(symbol, "initializer", None) is not None:
            return None
        width, two_state = shape
        init = ({"kind": "Literal", "span": None, "width": width,
                 "bits": "0" * width} if two_state else None)
        return signed_metadata({
            "kind": "Var", "span": sym_span(sm, symbol),
            "name": _storage_name(symbol), "width": width, "init": init,
            "unpacked_union_cell": True,
        }, symbol.type)
    except Exception:
        return None


def _unpacked_union_whole_copy(sm, expression):
    """Lower a blocking whole-copy between shallow unpacked unions.

    An admitted union declaration is already one flat vector cell, so a
    whole-value assignment can copy that cell directly.  Keep the operation
    blocking and require equal width/state shape; scheduled or aggregate
    forms still need their own publication and storage rules.
    """
    try:
        if (type(expression).__name__ != "AssignmentExpression"
                or expression.op is not None
                or expression.timingControl is not None
                or expression.isNonBlocking):
            return None
        left = expression.left
        right = expression.right
        if (not _storage_expression(left) or not _storage_expression(right)
                or str(left.symbol.kind) not in ("SymbolKind.Variable", "SymbolKind.Net")
                or str(right.symbol.kind) not in ("SymbolKind.Variable", "SymbolKind.Net")):
            return None
        left_shape = _unpacked_union_shape(left.type)
        right_shape = _unpacked_union_shape(right.type)
        if left_shape is None or left_shape != right_shape:
            return None
        width, two_state = left_shape
        target = {"kind": "Ident", "span": node_span(sm, left),
                  "width": width, "name": _storage_name(left.symbol)}
        value = {"kind": "Ident", "span": node_span(sm, right),
                 "width": width, "name": _storage_name(right.symbol)}
        if two_state:
            value = squash2_wrap(value, width)
        return {"kind": "BlockingAssign", "span": node_span(sm, expression),
                "target": target, "value": value,
                "unpacked_union_whole_copy_lowered": True}
    except Exception:
        return None


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


def _fixed_real_bits_call_width(expression):
    """Return the fixed width of a pure real-to-bit conversion call."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName not in ("$realtobits", "$shortrealtobits")
                or len(expression.arguments) != 1):
            return None
        argument = expression.arguments[0]
        if (getattr(argument, "bad", False)
                or type(argument.type.canonicalType).__name__ != "FloatingType"
                or not expression.type.isIntegral):
            return None
        width = 64 if expression.subroutineName == "$realtobits" else 32
        if expression.type.bitWidth != width:
            return None
        return width
    except Exception:
        return None


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
        if _SYM is None and _fixed_real_bits_call_width(node) is not None:
            pure = pure and _bits_argument_source_ok(node.arguments[0])
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
                or expression.type.bitWidth != 32
                or not expression.type.isSigned
                or not _bits_argument_source_ok(argument)):
            return None
        if (argument.type.isBitstreamType()):
            return argument.type.bitstreamWidth
        # IEEE 1800 §6.24.3 defines real and shortreal as fixed-size types
        # for `$bits(type)` even though their runtime values are opaque to the
        # flat self-check store. A DataTypeExpression is type inspection only;
        # a named real value remains outside this metadata-only slice.
        if (type(argument).__name__ == "DataTypeExpression"
                and type(argument.type.canonicalType).__name__ == "FloatingType"
                and argument.type.bitWidth in (32, 64)):
            return argument.type.bitWidth
        return None
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


def _empty_dynamic_bits_query(expression):
    """Recognize ``$bits`` of an empty dynamic array or string variable."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$bits"
                or len(expression.arguments) != 1):
            return False
        argument = expression.arguments[0]
        if (type(argument).__name__ != "NamedValueExpression"
                or getattr(argument, "bad", False)):
            return False
        canonical = type(argument.type.canonicalType).__name__
        if canonical not in ("DynamicArrayType", "StringType"):
            return False
        width, _two_state, reason = type_width_2s(expression.type)
        if (width != 32 or reason is not None
                or not expression.type.isIntegral or not expression.type.isSigned):
            return False
        symbol = getattr(argument, "symbol", None)
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if symbol is None or not name or not source:
            return False
        initializer = getattr(symbol, "initializer", None)
        if canonical == "DynamicArrayType":
            if initializer is not None:
                return False
        elif initializer is not None:
            while type(initializer).__name__ == "ConversionExpression":
                initializer = getattr(initializer, "operand", None)
            if (type(initializer).__name__ != "StringLiteral"
                    or getattr(initializer, "value", None) != ""):
                return False
        code_source = _sv_code_source(source)
        occurrences = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", code_source))
        if not occurrences:
            return False
        for occurrence in occurrences[1:]:
            prefix = code_source[:occurrence.start()].rstrip()
            suffix = code_source[occurrence.end():].lstrip()
            if not (re.search(r"\$bits\s*\(\s*$", prefix)
                    and suffix.startswith(")")):
                return False
        return True
    except Exception:
        return False


def _convert_empty_dynamic_bits_query(sm, expression):
    if not _empty_dynamic_bits_query(expression):
        return unsupported(sm, expression, "CallExpression:bits-empty-dynamic")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": 32, "bits": "0" * 32,
        "empty_dynamic_bits_query": True,
    }, expression.type)


BIT_QUERY_CALLS = ("$countbits", "$countones", "$onehot", "$onehot0", "$isunknown")
SIGNING_CALLS = ("$signed", "$unsigned")
ENUM_NUMERIC_METHODS = ("first", "last", "next", "prev", "num")
DIMENSION_QUERY_CALLS = (
    "$size", "$high", "$left", "$right", "$low", "$increment",
    "$dimensions", "$unpacked_dimensions",
)


def _isunbounded_call(expression):
    """Recognize ``$isunbounded`` on a known bounded integral parameter.

    IEEE 1800-2023 §6.20.7 defines the result as one only for the special
    unbounded value ``$``.  A literal or a bound parameter is therefore a
    pure one-bit zero; ordinary variables and an unbounded parameter stay
    loud because their value is not represented by the self-check state.
    """
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or expression.bad or not expression.isSystemCall
                or expression.subroutineName != "$isunbounded"
                or len(expression.arguments) != 1
                or expression.type.bitWidth != 1):
            return False
        argument = expression.arguments[0]
        if not _case_source_expression_ok(argument):
            return False
        if _literal_integral_value(argument) is not None:
            return True
        symbol = getattr(argument, "symbol", None)
        if symbol is None or str(getattr(symbol, "kind", "")).split(".")[-1] != "Parameter":
            return False
        # pyslang exposes a bounded parameter's elaborated value as an
        # integral ``ConstantValue``.  The unbounded `$` value has no SVInt
        # payload, so it cannot pass this test.
        constant = getattr(getattr(symbol, "value", None), "value", None)
        return (type(constant).__name__ == "SVInt"
                and not any(bit not in "01" for bit in svint_bits(constant)))
    except Exception:
        return False


def _coverage_call(expression):
    """Recognize a literal-argument coverage query in the empty DB model.

    The legacy self-check state has no covergroup, coverage counter, or
    external coverage database.  IEEE permits ``SV_COV_NOCOV`` (zero) for
    each of these queries when no coverage is available, so a call whose
    control and scope arguments are literals can be represented by a plain
    signed 32-bit zero.  A dynamic argument or any source coverage construct
    stays at the call boundary rather than receiving a guessed result.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName not in COVERAGE_CALLS):
            return False
        args = list(expression.arguments)
        arities = {
            "$coverage_control": 4,
            "$coverage_get": 3,
            "$coverage_get_max": 3,
            "$coverage_merge": 2,
            "$coverage_save": 2,
        }
        if len(args) != arities[expression.subroutineName]:
            return False
        integral_count = {
            "$coverage_control": 3,
            "$coverage_get": 2,
            "$coverage_get_max": 2,
            "$coverage_merge": 1,
            "$coverage_save": 1,
        }[expression.subroutineName]
        for argument in args[:integral_count]:
            if not _integral_literal_source(argument):
                return False
        for argument in args[integral_count:]:
            # Contextual string arguments are represented by pyslang as a
            # ConversionExpression around the source StringLiteral.  Peel
            # that elaboration shell, while keeping names and computed string
            # expressions outside this literal-only query slice.
            node = argument
            while type(node).__name__ == "ConversionExpression":
                node = getattr(node, "operand", None)
                if node is None:
                    return False
            if (type(node).__name__ != "StringLiteral"
                    or getattr(node, "bad", False)):
                return False
        source = (_SOURCE_BYTES.decode("utf-8", errors="replace")
                  if _SOURCE_BYTES else "")
        masked = _sv_code_source(source)
        if re.search(r"\bcovergroup\b|\bcoverpoint\b|\bbins\b|\bcross\b",
                     masked):
            return False
        width, _two_state, reason = type_width_2s(expression.type)
        return (getattr(expression.type, "isIntegral", False)
                and width == 32 and reason is None)
    except Exception:
        return False


def _convert_coverage_call(sm, expression):
    if not _coverage_call(expression):
        return unsupported(sm, expression,
                           "CallExpression:" + getattr(expression,
                                                        "subroutineName",
                                                        "coverage"))
    return signed_metadata({
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": 32,
        "bits": "0" * 32,
        "coverage_nocov": True,
    }, expression.type)


def _convert_isunbounded(sm, expression):
    if not _isunbounded_call(expression):
        return unsupported(sm, expression, "CallExpression:$isunbounded")
    return {
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": 1,
        "bits": "0",
        "isunbounded_bounded": True,
    }


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
    if method == "name":
        if len(arguments) != 1 or not members:
            return unsupported(sm, expression, "EnumMethod:signature")
        subject = convert_expr(sm, receiver)
        if subject is None or not _case_expression_ok(subject):
            return unsupported(sm, expression, "EnumMethod:operand")
        cases = []
        for member in members:
            value = member.value.value
            width, _, reason = type_width_2s(receiver.type)
            if (reason is not None or type(value).__name__ != "SVInt"
                    or value.bitWidth != width):
                return unsupported(sm, expression, "EnumMethod:member-type")
            cases.append({
                "value": {
                    "kind": "Literal",
                    "span": node_span(sm, expression),
                    "width": width,
                    "bits": svint_bits(value),
                },
                "name": member.name,
            })
        return {
            "kind": "EnumName",
            "span": node_span(sm, expression),
            "subject": subject,
            "cases": cases,
            "default": "",
            "enum_name_lowered": True,
        }
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


def _fopen_invalid_mode_call(expression):
    """Recognize the deterministic zero result for an invalid `$fopen` mode."""
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or not expression.isSystemCall
                or expression.subroutineName != "$fopen"
                or len(expression.arguments) != 2
                or expression.type.bitWidth != 32
                or not expression.type.isIntegral):
            return False
        path, mode = expression.arguments
        while type(path).__name__ == "ConversionExpression":
            path = path.operand
        while type(mode).__name__ == "ConversionExpression":
            mode = mode.operand
        if (type(path).__name__ != "StringLiteral"
                or type(mode).__name__ != "StringLiteral"
                or getattr(path, "bad", False) or getattr(mode, "bad", False)):
            return False
        # IEEE 21.3.1 permits r/w/a with optional +; every other literal mode
        # is rejected before any file operation is attempted.
        return mode.value not in ("r", "w", "a", "r+", "w+", "a+")
    except Exception:
        return False


def _convert_fopen_invalid_mode(sm, expression):
    if not _fopen_invalid_mode_call(expression):
        return unsupported(sm, expression, "CallExpression:$fopen")
    return {"kind": "Literal", "span": node_span(sm, expression),
            "width": 32, "bits": "0" * 32,
            "fopen_invalid_mode": True}


def _fseek_stdout_error_call(expression):
    """Recognize the deterministic error for seeking predefined stdout.

    The flat self-check state represents stdout only as the predefined MCD
    used by the formatted-output tasks; it has no seekable file object.  IEEE
    1800 therefore gives the literal ``$fseek(32'h8000_0001, 0, 0)`` probe
    the standard error result ``-1``.  Dynamic descriptors, offsets, and
    whence values remain at the file-state boundary.
    """
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$fseek"
                or len(expression.arguments) != 3
                or expression.type.bitWidth != 32
                or not expression.type.isIntegral
                or not expression.type.isSigned):
            return False
        fd, offset, whence = expression.arguments
        return (_literal_integral_value(fd) == 0x80000001
                and _literal_integral_value(offset) == 0
                and _literal_integral_value(whence) == 0)
    except Exception:
        return False


def _convert_fseek_stdout_error(sm, expression):
    if not _fseek_stdout_error_call(expression):
        return unsupported(sm, expression, "CallExpression:$fseek")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": 32, "bits": "1" * 32,
        "fseek_stdout_error": True,
    }, expression.type)


def _ftell_stdout_error_call(expression):
    """Recognize the deterministic error for querying predefined stdout.

    The self-check state has no seekable file object for the predefined stdout
    descriptor, so IEEE 1800's ``$ftell`` error result is the literal ``-1``.
    Dynamic descriptors remain at the external file-state boundary.
    """
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$ftell"
                or len(expression.arguments) != 1
                or expression.type.bitWidth != 32
                or not expression.type.isIntegral
                or not expression.type.isSigned):
            return False
        return _literal_integral_value(expression.arguments[0]) == 0x80000001
    except Exception:
        return False


def _convert_ftell_stdout_error(sm, expression):
    if not _ftell_stdout_error_call(expression):
        return unsupported(sm, expression, "CallExpression:$ftell")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": 32, "bits": "1" * 32,
        "ftell_stdout_error": True,
    }, expression.type)


def _stime_call(expression):
    """A zero-argument `$stime` query in the time-zero self-check slice."""
    try:
        return (type(expression).__name__ == "CallExpression"
                and not expression.bad and expression.isSystemCall
                and expression.subroutineName == "$stime"
                and len(expression.arguments) == 0
                and expression.type.isIntegral)
    except Exception:
        return False


def _realtime_call(expression):
    """A zero-argument `$realtime` query in the time-zero self-check slice."""
    try:
        return (type(expression).__name__ == "CallExpression"
                and not expression.bad and expression.isSystemCall
                and expression.subroutineName == "$realtime"
                and len(expression.arguments) == 0)
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


def _convert_stime_call(sm, expression):
    if not _stime_call(expression):
        return unsupported(sm, expression, "CallExpression:$stime")
    return {
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": expression.type.bitWidth,
        "bits": "0" * expression.type.bitWidth,
        "time_zero": True,
    }


_TIME_UNIT_EXPONENTS = {
    "s": 0, "ms": -3, "us": -6, "ns": -9, "ps": -12, "fs": -15,
}


def _time_scale_call(expression):
    try:
        return (type(expression).__name__ == "CallExpression"
                and expression.isSystemCall
                and expression.subroutineName in ("$timeunit", "$timeprecision")
                and not expression.arguments)
    except Exception:
        return False


def _convert_time_scale_call(sm, expression):
    """Fold `$timeunit`/`$timeprecision` from a literal source timescale."""
    try:
        if (not _time_scale_call(expression) or expression.type.bitWidth != 32
                or not expression.type.isSigned):
            return None
        text = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        matches = list(re.finditer(
            r"`timescale\s+(?:1\s*)?([munpf]?s)\s*/\s*(?:1\s*)?([munpf]?s)",
            text, flags=re.IGNORECASE))
        if not matches:
            return None
        match = matches[-1]
        unit = match.group(1 if expression.subroutineName == "$timeunit" else 2).lower()
        exponent = _TIME_UNIT_EXPONENTS.get(unit)
        if exponent is None:
            return None
        return {"kind": "Literal", "span": node_span(sm, expression),
                "width": 32, "bits": format(exponent & 0xffffffff, "032b"),
                "signed": True, "time_scale_query": expression.subroutineName}
    except Exception:
        return None


def _convert_time_literal(sm, expression):
    """Convert a finite time literal to the integral time representation."""
    try:
        value = int(round(float(expression.value)))
        width = expression.type.bitWidth
        if width <= 0 or value < 0:
            return unsupported(sm, expression, "TimeLiteral:value")
        return {
            "kind": "Literal",
            "span": node_span(sm, expression),
            "width": width,
            "bits": format(value & ((1 << width) - 1), f"0{width}b"),
            "time_literal": True,
        }
    except Exception:
        return unsupported(sm, expression, "TimeLiteral:value")


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
_ARRAY_REDUCTION_INDICES = {}
_ASSOC_CELLS = {}


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


def _assoc_key_binding(expression, symbol, kind):
    """Resolve a selector through one immutable literal local binding.

    The finite associative-cell lowering can represent a named selector when
    its declaration initializer is a literal and the containing scope never
    assigns that selector again.  A later assignment would make the cell name
    depend on runtime state, so it deliberately remains outside this path.
    """
    try:
        if type(expression).__name__ != "NamedValueExpression":
            return None
        bound = getattr(expression, "symbol", None)
        if bound is None or bound is symbol:
            return None
        initializer = getattr(bound, "initializer", None)
        if initializer is None:
            return None
        if kind == "string":
            value = _assoc_string_key(initializer)
        else:
            value = _assoc_integral_key(initializer)
        if value is None:
            return None
        instance = getattr(getattr(bound, "parentScope", None),
                           "containingInstance", None)
        if instance is None:
            return None
        rebound = False

        def inspect(node):
            nonlocal rebound
            if type(node).__name__ != "AssignmentExpression":
                return
            left = getattr(node, "left", None)
            rebound = rebound or (
                type(left).__name__ == "NamedValueExpression"
                and getattr(left, "symbol", None) is bound)

        instance.visit(inspect)
        return None if rebound else value
    except Exception:
        return None


def _assoc_string_key(expression, symbol=None):
    """Return a small literal string associative-array key, else ``None``."""
    node = expression
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return None
    if (type(node).__name__ != "StringLiteral" or getattr(node, "bad", False)
            or any(ord(char) > 127 for char in getattr(node, "value", ""))):
        return _assoc_key_binding(expression, symbol, "string") if symbol is not None else None
    return node.value


def _finite_string_assoc_cells(sm, symbol):
    """Collect a finite, literal-key string associative array.

    The self-check state has no associative-array object.  A source that only
    selects a finite set of literal string keys can use one ordinary scalar
    cell per key without changing the value or statement schemas.  Any whole
    array, dynamic-key, method, or non-integral-element use rejects the whole
    declaration so the fallback remains loud.
    """
    try:
        if (str(getattr(symbol, "kind", "")) != "SymbolKind.Variable"
                or type(symbol.type.canonicalType).__name__ != "AssociativeArrayType"):
            return None
        array_type = symbol.type.canonicalType
        index_type = array_type.indexType.canonicalType
        if type(index_type).__name__ != "StringType":
            return None
        element_type = array_type.elementType
        width, two_state, reason = type_width_2s(element_type)
        if width is None or reason is not None or width <= 0:
            return None
        instance = symbol.parentScope.containingInstance
        if instance is None:
            return None
        keys = {}
        named_count = 0
        selected_count = 0
        invalid = False

        def inspect(node):
            nonlocal named_count, selected_count, invalid
            kind = type(node).__name__
            if kind == "ElementSelectExpression":
                value = getattr(node, "value", None)
                if getattr(value, "symbol", None) is symbol:
                    selected_count += 1
                    key = _assoc_string_key(getattr(node, "selector", None), symbol)
                    if key is None:
                        invalid = True
                    else:
                        keys.setdefault(key, None)
            elif kind in ("NamedValueExpression", "HierarchicalValueExpression"):
                if getattr(node, "symbol", None) is symbol:
                    named_count += 1

        instance.visit(inspect)
        if invalid or not keys or named_count != selected_count:
            return None
        base = _array_storage_name(symbol)
        cells = {}
        for key in keys:
            encoded = key.encode("ascii").hex()
            cells[key] = {
                "name": f"{base}[string:{encoded}]",
                "width": width,
                "two_state": two_state,
            }
        _ASSOC_CELLS[symbol] = cells
        return cells
    except Exception:
        return None


def _finite_string_assoc_decls(sm, symbol):
    cells = _ASSOC_CELLS.get(symbol)
    if cells is None:
        cells = _finite_string_assoc_cells(sm, symbol)
    if cells is None:
        return None
    width = next(iter(cells.values()))["width"]
    two_state = next(iter(cells.values()))["two_state"]
    return [signed_metadata({
        "kind": "Var", "span": sym_span(sm, symbol),
        "name": cell["name"], "width": width,
        "init": ({"kind": "Literal", "span": None, "width": width,
                   "bits": "0" * width} if two_state else None),
    }, symbol.type.elementType) for cell in cells.values()]


def _finite_string_assoc_cell(sm, expression):
    if _SYM is not None or type(expression).__name__ != "ElementSelectExpression":
        return None
    value = getattr(expression, "value", None)
    symbol = getattr(value, "symbol", None)
    if symbol is None:
        return None
    cells = _ASSOC_CELLS.get(symbol)
    if cells is None:
        cells = _finite_string_assoc_cells(sm, symbol)
    if cells is None:
        return None
    key = _assoc_string_key(getattr(expression, "selector", None), symbol)
    if key not in cells:
        return None
    return cells[key]


def _assoc_integral_key(expression, symbol=None):
    """Return a known integral associative-array key, else ``None``."""
    try:
        value = _literal_integral_value(expression)
        if value is not None:
            return value
        return _assoc_key_binding(expression, symbol, "integral") if symbol is not None else None
    except Exception:
        return None


def _finite_integral_assoc_cells(sm, symbol):
    """Collect a finite, literal-key integral associative array.

    Like the finite string-key lowering above, this replaces each observed
    literal key with one ordinary scalar cell.  The array must be used only
    through literal integral selections and its element type must already fit
    the flat scalar state; dynamic keys, whole-array operations, methods, and
    other aggregate elements stay loud.
    """
    try:
        if (str(getattr(symbol, "kind", "")) != "SymbolKind.Variable"
                or type(symbol.type.canonicalType).__name__ != "AssociativeArrayType"):
            return None
        array_type = symbol.type.canonicalType
        index_type = array_type.indexType.canonicalType
        if not getattr(index_type, "isIntegral", False):
            return None
        element_type = array_type.elementType
        width, two_state, reason = type_width_2s(element_type)
        if width is None or reason is not None or width <= 0:
            return None
        instance = symbol.parentScope.containingInstance
        if instance is None:
            return None
        keys = {}
        named_count = 0
        selected_count = 0
        invalid = False

        def inspect(node):
            nonlocal named_count, selected_count, invalid
            kind = type(node).__name__
            if kind == "ElementSelectExpression":
                value = getattr(node, "value", None)
                if getattr(value, "symbol", None) is symbol:
                    selected_count += 1
                    key = _assoc_integral_key(getattr(node, "selector", None), symbol)
                    if key is None:
                        invalid = True
                    else:
                        keys.setdefault(key, None)
            elif kind in ("NamedValueExpression", "HierarchicalValueExpression"):
                if getattr(node, "symbol", None) is symbol:
                    named_count += 1

        instance.visit(inspect)
        if invalid or not keys or named_count != selected_count:
            return None
        base = _array_storage_name(symbol)
        cells = {}
        for key in keys:
            cells[key] = {
                "name": f"{base}[int:{key}]",
                "width": width,
                "two_state": two_state,
            }
        _ASSOC_CELLS[symbol] = cells
        return cells
    except Exception:
        return None


def _finite_integral_assoc_decls(sm, symbol):
    cells = _ASSOC_CELLS.get(symbol)
    if cells is None:
        cells = _finite_integral_assoc_cells(sm, symbol)
    if cells is None:
        return None
    return [signed_metadata({
        "kind": "Var", "span": sym_span(sm, symbol),
        "name": cell["name"], "width": cell["width"],
        "init": ({"kind": "Literal", "span": None,
                   "width": cell["width"], "bits": "0" * cell["width"]}
                  if cell["two_state"] else None),
    }, symbol.type.elementType) for cell in cells.values()]


def _finite_integral_assoc_cell(sm, expression):
    if _SYM is not None or type(expression).__name__ != "ElementSelectExpression":
        return None
    value = getattr(expression, "value", None)
    symbol = getattr(value, "symbol", None)
    if symbol is None:
        return None
    cells = _ASSOC_CELLS.get(symbol)
    if cells is None:
        cells = _finite_integral_assoc_cells(sm, symbol)
    if cells is None:
        return None
    key = _assoc_integral_key(getattr(expression, "selector", None), symbol)
    if key not in cells:
        return None
    return cells[key]


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
        seen = set()
        while type(current).__name__ == "FixedSizeUnpackedArrayType":
            marker = id(current)
            if marker in seen or len(dimensions) >= 64:
                return None
            seen.add(marker)
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


def _dynamic_array_element_shape(element_type):
    """Return nested fixed dimensions and an integral leaf for one element.

    A dynamic outer dimension can be represented by the same flat cells as a
    fixed unpacked array when every inner dimension is finite and the final
    leaf is scalar or packed integral.  Dynamic/queue/associative inner
    dimensions and aggregate leaves remain outside that representation.
    """
    try:
        nested = _fixed_array_dimensions(element_type, max_cells=1024)
        if nested is not None:
            dimensions, leaf_type = nested
            width, two_state, reason = type_width_2s(leaf_type)
            if width is None or reason is not None:
                return None
            return dimensions, leaf_type, width, two_state
        width, two_state, reason = type_width_2s(element_type)
        if width is None or reason is not None:
            return None
        return [], element_type, width, two_state
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
        source_symbol = None
        if _storage_expression(current):
            source_name = _array_storage_name(current.symbol)
            source_type = current.type
            source_symbol = current.symbol
        else:
            path = _unpacked_struct_path(current)
            if path is None:
                return None
            source_name, selected_type = path
            source_type = selected_type
            root = current
            while type(root).__name__ == "MemberAccessExpression":
                root = root.value
            if not _storage_expression(root):
                return None
            source_symbol = root.symbol
        if str(source_symbol.kind) not in ("SymbolKind.Variable", "SymbolKind.Net"):
            return None
        if type(source_type.canonicalType).__name__ == "DynamicArrayType":
            # A dynamic array field has no independent symbol from which to
            # recover a sampled extent; keep that aggregate boundary loud.
            if not _storage_expression(current):
                return None
            count = _dynamic_array_constant_extent(current.symbol)
            if count is None:
                return None
            inner = _dynamic_array_element_shape(
                current.type.canonicalType.elementType)
            if inner is None:
                element_type = current.type.canonicalType.elementType
                if type(element_type.canonicalType).__name__ != "UnpackedStructType":
                    return None
                shape = ([(0, count - 1)], element_type)
            else:
                inner_dimensions, leaf_type, _width, _two_state = inner
                shape = ([(0, count - 1)] + inner_dimensions, leaf_type)
        else:
            shape = _fixed_array_dimensions(source_type, max_cells=None)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        if len(selectors) != len(dimensions):
            return None
        positions = list(reversed(selectors))
        for position, (left, right) in zip(positions, dimensions):
            if position < min(left, right) or position > max(left, right):
                return None
        name = source_name
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
    """Recognize a fully constant out-of-bounds array selection.

    A dynamic array is admitted here only after its one constant ``new[N]``
    allocation has been sampled by ``_dynamic_array_constant_extent``.  SV
    specifies that a constant out-of-range element write has no effect; the
    flat cell store can therefore erase that write without inventing a dynamic
    array object.  Resizes, dynamic indices, and unsupported leaves stay loud.
    """
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
        if type(current.type.canonicalType).__name__ == "DynamicArrayType":
            count = _dynamic_array_constant_extent(current.symbol)
            if count is None:
                return False
            inner = _dynamic_array_element_shape(
                current.type.canonicalType.elementType)
            if inner is None:
                element_type = current.type.canonicalType.elementType
                if type(element_type.canonicalType).__name__ != "UnpackedStructType":
                    return False
                shape = ([(0, count - 1)], element_type)
            else:
                inner_dimensions, leaf_type, _width, _two_state = inner
                shape = ([(0, count - 1)] + inner_dimensions, leaf_type)
        else:
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


def _fixed_array_oob_read(sm, expression):
    """Return ``(width, two_state)`` for a constant fixed-array OOB read.

    IEEE 1800-2023 §7.4.5 gives an out-of-bounds unpacked-array read the
    element type's default value: all zeroes for a two-state element and all
    x for a four-state element.  The flat state can represent that result
    without inventing an aggregate slot, but only for a fully constant,
    finite unpacked array with an integral leaf.  Dynamic indices, dynamic
    arrays, aggregate leaves, and packed/scalar selections remain loud.
    """
    try:
        if type(expression).__name__ != "ElementSelectExpression":
            return None
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
        if type(current.type.canonicalType).__name__ != "FixedSizeUnpackedArrayType":
            return None
        shape = _fixed_array_dimensions(current.type, max_cells=None)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        if len(selectors) != len(dimensions):
            return None
        if not any(position < min(left, right) or position > max(left, right)
                   for position, (left, right) in
                   zip(reversed(selectors), dimensions)):
            return None
        width, two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None:
            return None
        return width, two_state
    except Exception:
        return None


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


def _fixed_array_constant_uses(symbol):
    """Collect constant one-dimensional selections of a fixed array symbol.

    Large fixed arrays are represented sparsely in the flat self-check state:
    only cells that the source selects at a constant index are materialized.
    A dynamic or aggregate use is deliberately rejected, because a finite
    list of cells cannot stand in for that operation.
    """
    try:
        instance = symbol.parentScope.containingInstance
        uses = set()
        named_count = 0
        selected_count = 0

        def inspect(node):
            nonlocal named_count, selected_count
            kind = type(node).__name__
            if kind == "ElementSelectExpression":
                value = node.value
                if (type(value).__name__ == "NamedValueExpression"
                        and getattr(value, "symbol", None) is symbol):
                    selected_count += 1
                    position = _constant_dimension_selector(node.selector)
                    if position is None:
                        uses.add(None)
                    else:
                        uses.add(position)
            elif kind in ("NamedValueExpression", "HierarchicalValueExpression"):
                if getattr(node, "symbol", None) is symbol:
                    named_count += 1

        instance.visit(inspect)
        if None in uses or named_count != selected_count:
            return None
        return sorted(uses)
    except Exception:
        return None


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
        if (_SYM is None and type(value).__name__ == "NamedValueExpression"
                and getattr(value, "symbol", None) in _ARRAY_REDUCTION_VALUES):
            bound = _ARRAY_REDUCTION_VALUES[value.symbol]
            aggregate = bound.get("aggregate") if isinstance(bound, dict) else None
            aggregate_leaf = (aggregate.canonicalType if aggregate is not None
                              else None)
            if (aggregate_leaf is not None
                    and type(aggregate_leaf).__name__ == "UnpackedStructType"):
                member = expression.member
                width, two_state, reason = type_width_2s(member.type)
                leaf = member.type.canonicalType
                if (width is None or reason is not None
                        or type(leaf).__name__ in ("FixedSizeUnpackedArrayType",
                                                    "DynamicArrayType", "QueueType",
                                                    "AssociativeArrayType",
                                                    "UnpackedStructType", "UnpackedUnionType")):
                    return None
                return {"name": f"{bound['name']}.{member.name}",
                        "width": width, "two_state": two_state}
        if (_SYM is None and type(value).__name__ == "NamedValueExpression"
                and str(getattr(getattr(value, "symbol", None), "kind", ""))
                == "SymbolKind.Iterator"
                and type(value.type.canonicalType).__name__ == "UnpackedStructType"):
            member = expression.member
            width, two_state, reason = type_width_2s(member.type)
            leaf = member.type.canonicalType
            if (width is None or reason is not None
                    or type(leaf).__name__ in ("FixedSizeUnpackedArrayType",
                                                "DynamicArrayType", "QueueType",
                                                "AssociativeArrayType",
                                                "UnpackedStructType", "UnpackedUnionType")):
                return None
            return {"name": f"$iterator.{member.name}",
                    "width": width, "two_state": two_state}
        path = _unpacked_struct_path(value)
        if path is None:
            return None
        base_name, aggregate = path
        aggregate_kind = type(aggregate).__name__
        if aggregate_kind == "UnpackedUnionType":
            shape = _unpacked_union_shape(aggregate)
            if shape is None:
                return None
            width, two_state = shape
            member = expression.member
            member_width, member_two_state, reason = type_width_2s(member.type)
            if (member_width != width or reason is not None
                    or bool(member_two_state) != bool(two_state)):
                return None
            return {"name": base_name, "width": width,
                    "two_state": two_state}
        if aggregate_kind != "UnpackedStructType":
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


def _unpacked_struct_path(expression):
    """Return the flattened name and aggregate type for a struct receiver."""
    try:
        if _storage_expression(expression):
            return _storage_name(expression.symbol), expression.type.canonicalType
        if type(expression).__name__ == "MemberAccessExpression":
            parent = _unpacked_struct_path(expression.value)
            if parent is None:
                return None
            parent_name, parent_type = parent
            if type(parent_type).__name__ != "UnpackedStructType":
                return None
            member = expression.member
            if member.type.canonicalType is None:
                return None
            return f"{parent_name}.{member.name}", member.type.canonicalType
        # Only element selections can reach the fixed-array helper here.
        # Calling it for a member access would recurse back into this
        # function while it tries to resolve that same member path.
        if type(expression).__name__ == "ElementSelectExpression":
            selected = _fixed_array_selection_prefix(expression)
            if selected is not None:
                return selected[0], selected[1].canonicalType
        return None
    except Exception:
        return None


def _unpacked_struct_field_cells(base_name, aggregate, span, seen=None):
    """Flatten an integral-only unpacked-struct tree into vector cells."""
    if seen is None:
        seen = set()
    marker = id(aggregate)
    if marker in seen or type(aggregate).__name__ != "UnpackedStructType":
        return None
    seen = seen | {marker}
    fields = list(aggregate)
    if not fields:
        return None
    cells = []
    for field in fields:
        leaf = field.type.canonicalType
        if type(leaf).__name__ == "UnpackedStructType":
            nested = _unpacked_struct_field_cells(
                f"{base_name}.{field.name}", leaf, span, seen)
            if nested is None:
                return None
            cells.extend(nested)
            continue
        if type(leaf).__name__ == "FixedSizeUnpackedArrayType":
            array_shape = _fixed_array_dimensions(field.type, max_cells=1024)
            if array_shape is None:
                return None
            dimensions, array_leaf = array_shape
            width, two_state, reason = type_width_2s(array_leaf)
            if (width is None or reason is not None or
                    type(array_leaf.canonicalType).__name__ in (
                        "FixedSizeUnpackedArrayType", "DynamicArrayType",
                        "QueueType", "AssociativeArrayType",
                        "UnpackedStructType", "UnpackedUnionType")):
                return None
            positions = [()]
            for left, right in dimensions:
                step = 1 if right >= left else -1
                positions = [prefix + (position,)
                             for prefix in positions
                             for position in range(left, right + step, step)]
            for indexes in positions:
                name = f"{base_name}.{field.name}" + "".join(
                    f"[{position}]" for position in indexes)
                init = ({"kind": "Literal", "span": None, "width": width,
                         "bits": "0" * width} if two_state else None)
                cells.append((name, width, init, array_leaf))
            continue
        width, two_state, reason = type_width_2s(field.type)
        if width is None or reason is not None:
            return None
        if type(leaf).__name__ in ("FixedSizeUnpackedArrayType",
                                   "DynamicArrayType", "QueueType",
                                   "AssociativeArrayType", "UnpackedUnionType"):
            return None
        init = ({"kind": "Literal", "span": None, "width": width,
                 "bits": "0" * width} if two_state else None)
        cells.append((f"{base_name}.{field.name}", width, init, field.type))
    return cells


def _unpacked_struct_initializer_cells(sm, base_name, aggregate, initializer,
                                       seen=None):
    """Flatten a complete nested struct assignment pattern into leaf cells.

    Fixed unpacked array fields are finite in the legacy store just like the
    scalar fields around them.  Slang elaborates a struct ``default``/keyed
    default into one pattern value per field, with an array field's value
    carrying its own complete element pattern.  Expand that inner pattern in
    declaration order so a procedural write can use the same cells as a
    declaration initializer.
    """
    if seen is None:
        seen = set()
    marker = id(aggregate)
    if marker in seen or type(aggregate).__name__ != "UnpackedStructType":
        return None
    if type(initializer).__name__ not in (
            "SimpleAssignmentPatternExpression",
            "StructuredAssignmentPatternExpression"):
        return None
    if getattr(initializer, "bad", False):
        return None
    fields = list(aggregate)
    elements = list(initializer.elements)
    if not fields or len(fields) != len(elements):
        return None
    seen = seen | {marker}
    cells = []
    for field, value in zip(fields, elements):
        leaf = field.type.canonicalType
        name = f"{base_name}.{field.name}"
        if type(leaf).__name__ == "UnpackedStructType":
            nested = _unpacked_struct_initializer_cells(
                sm, name, leaf, value, seen)
            if nested is None:
                return None
            cells.extend(nested)
            continue
        if type(leaf).__name__ == "FixedSizeUnpackedArrayType":
            shape = _fixed_array_dimensions(field.type, max_cells=1024)
            if shape is None:
                return None
            dimensions, array_leaf = shape
            width, two_state, reason = type_width_2s(array_leaf)
            if (width is None or reason is not None
                    or type(array_leaf.canonicalType).__name__ in (
                        "FixedSizeUnpackedArrayType", "DynamicArrayType",
                        "QueueType", "AssociativeArrayType",
                        "UnpackedStructType", "UnpackedUnionType")):
                return None
            elements = _fixed_array_pattern_elements(value, dimensions)
            if elements is None:
                return None
            positions = [()]
            for left, right in dimensions:
                step = 1 if right >= left else -1
                positions = [prefix + (position,)
                             for prefix in positions
                             for position in range(left, right + step, step)]
            if len(elements) != len(positions):
                return None
            for indexes, element in zip(positions, elements):
                if (element is None
                        or not _case_source_expression_ok(
                            element, packed_members=True)):
                    return None
                converted = convert_expr(sm, element)
                if (converted is None or converted.get("kind") == "Unsupported"
                        or width_of(converted) != width
                        or not _case_expression_ok(converted)):
                    return None
                if two_state:
                    converted = squash2_wrap(converted, width)
                cell_name = name + "".join(f"[{position}]"
                                            for position in indexes)
                cells.append((cell_name, width, converted, array_leaf))
            continue
        width, two_state, reason = type_width_2s(field.type)
        if width is None or reason is not None:
            return None
        if type(leaf).__name__ in ("FixedSizeUnpackedArrayType",
                                   "DynamicArrayType", "QueueType",
                                   "AssociativeArrayType", "UnpackedUnionType"):
            return None
        if value is None or not _case_source_expression_ok(value, packed_members=True):
            return None
        converted = convert_expr(sm, value)
        if (converted is None or converted.get("kind") == "Unsupported"
                or width_of(converted) != width
                or not _case_expression_ok(converted)):
            return None
        init = squash2_wrap(converted, width) if two_state else converted
        cells.append((name, width, init, field.type))
    return cells


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

        if any(type(field.type.canonicalType).__name__ in (
                "UnpackedStructType", "FixedSizeUnpackedArrayType")
               for field in fields):
            if initializer is None:
                cells = _unpacked_struct_field_cells(
                    _storage_name(symbol), aggregate, sym_span(sm, symbol))
            else:
                cells = _unpacked_struct_initializer_cells(
                    sm, _storage_name(symbol), aggregate, initializer)
            if cells is None:
                return None
            return [signed_metadata({
                "kind": "Var", "span": sym_span(sm, symbol), "name": name,
                "width": width, "init": init,
            }, field_type) for name, width, init, field_type in cells]

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
                                        "AssociativeArrayType", "UnpackedUnionType"):
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


def _dynamic_array_constant_extent(symbol):
    """Find the one constant ``new[N]`` allocation of a dynamic array.

    The flat self-check store can model a dynamic array after its size has
    been sampled, but it cannot represent a later resize or whole-array
    rebinding.  Accept exactly one constant allocation, either in the
    declaration or as a procedural assignment, and leave all other shapes
    loud.
    """
    try:
        if str(symbol.kind) != "SymbolKind.Variable":
            return None
        if type(symbol.type.canonicalType).__name__ != "DynamicArrayType":
            return None
        candidates = []
        initializer = getattr(symbol, "initializer", None)
        if initializer is not None:
            candidates.append(initializer)
        instance = symbol.parentScope.containingInstance
        if instance is None:
            return None
        whole_assignments = []

        def inspect(node):
            if type(node).__name__ != "AssignmentExpression":
                return
            lhs = getattr(node, "left", None)
            if (type(lhs).__name__ == "NamedValueExpression"
                    and getattr(lhs, "symbol", None) is symbol):
                whole_assignments.append(node.right)

        instance.visit(inspect)
        candidates.extend(whole_assignments)
        if len(candidates) == 2:
            first, second = candidates
            def allocation_parts(node):
                while type(node).__name__ == "ConversionExpression":
                    node = getattr(node, "operand", None)
                if type(node).__name__ != "NewArrayExpression":
                    return None
                size = getattr(node, "sizeExpr", None)
                if (type(size).__name__ != "IntegerLiteral"
                        or getattr(size, "bad", False)):
                    return None
                return int(getattr(size, "value", -1)), getattr(node, "initExpr", None)
            first_parts = allocation_parts(first)
            second_parts = allocation_parts(second)
            if first_parts is None or second_parts is None:
                return None
            first_count, first_init = first_parts
            second_count, second_init = second_parts
            while type(second_init).__name__ == "ConversionExpression":
                second_init = getattr(second_init, "operand", None)
            if (first_count <= 0 or second_count <= 0
                    or first_count > 1024 or second_count > 1024
                    or first_init is not None):
                return None
            element = symbol.type.canonicalType.elementType
            width, _two, reason = type_width_2s(element)
            if width is None or reason is not None:
                return None
            if type(second_init).__name__ == "NamedValueExpression":
                if getattr(second_init, "symbol", None) is not symbol:
                    return None
            elif second_init is not None:
                return None
            return second_count
        if len(candidates) != 1:
            return None
        allocation = candidates[0]
        if type(allocation).__name__ == "ConversionExpression":
            allocation = getattr(allocation, "operand", None)
        if type(allocation).__name__ != "NewArrayExpression":
            # A declaration-time positional literal pattern samples a finite
            # dynamic-array extent before the process starts.  The flat state
            # can represent that sampled shape exactly, provided the element
            # type is integral and every pattern element is a pure expression.
            # Keyed/default, nested aggregate, and effectful initializers stay
            # outside this object-free slice.
            if initializer is not None:
                pattern = initializer
                while type(pattern).__name__ == "ConversionExpression":
                    pattern = getattr(pattern, "operand", None)
                    if pattern is None:
                        return None
                if type(pattern).__name__ not in (
                        "SimpleAssignmentPatternExpression",
                        "StructuredAssignmentPatternExpression"):
                    return None
                elements = _pattern_source_elements(pattern)
                element_type = symbol.type.canonicalType.elementType
                width, _two, reason = type_width_2s(element_type)
                if (not elements or width is None or reason is not None
                        or any(not _case_source_expression_ok(element,
                                                               packed_members=True)
                               for element in elements)):
                    return None
                return len(elements) if len(elements) <= 1024 else None
            # An unpacked concatenation assigned to a dynamic array samples
            # its finite length at the assignment boundary.  The flat
            # self-check store can represent that sampled shape with the
            # same cells used by ``new[N]``.  Admit only scalar leaves and
            # exact nested assignment-pattern leaves; effectful or otherwise
            # aggregate RHSs remain loud instead of guessing their size.
            def literal_extent(node):
                kind = type(node).__name__
                if kind == "ConversionExpression":
                    return literal_extent(getattr(node, "operand", None))
                if kind == "ConcatenationExpression":
                    operands = list(getattr(node, "operands", []))
                    if not operands:
                        return None
                    total = 0
                    for operand in operands:
                        nested = literal_extent(operand)
                        if nested is None:
                            return None
                        total += nested
                    return total if total > 0 else None
                if kind == "NamedValueExpression":
                    # An unpacked fixed-array operand contributes each of its
                    # scalar cells to an unpacked concatenation.  A scalar
                    # named value remains one item.  Only integral leaf
                    # arrays are representable by the flat dynamic cells.
                    aggregate = getattr(getattr(node, "type", None),
                                        "canonicalType", None)
                    if type(aggregate).__name__ == "FixedSizeUnpackedArrayType":
                        dimensions, leaf = _fixed_array_dimensions(aggregate)
                        if dimensions is None:
                            return None
                        if type(getattr(leaf, "canonicalType", leaf)).__name__ in (
                                "FixedSizeUnpackedArrayType", "DynamicArrayType",
                                "QueueType", "AssociativeArrayType",
                                "UnpackedStructType", "UnpackedUnionType"):
                            return None
                        width, _two, reason = type_width_2s(leaf)
                        if width is None or reason is not None:
                            return None
                        count = 1
                        for left, right in dimensions:
                            count *= abs(int(left) - int(right)) + 1
                        return count if count > 0 else None
                    return 1
                if kind in ("SimpleAssignmentPatternExpression",
                            "StructuredAssignmentPatternExpression"):
                    elements = list(getattr(node, "elements", []))
                    if not elements:
                        return None
                    total = 0
                    for element in elements:
                        nested = literal_extent(element)
                        if nested is None:
                            # A scalar pattern element is one array cell;
                            # nested patterns recurse through the branch above.
                            if type(element).__name__ in (
                                    "IntegerLiteral", "UnbasedUnsizedIntegerLiteral",
                                    "NamedValueExpression", "UnaryExpression",
                                    "BinaryExpression", "ConditionalExpression"):
                                total += 1
                                continue
                            return None
                        total += nested
                    return total if total > 0 else None
                if kind in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral",
                            "UnaryExpression",
                            "BinaryExpression", "ConditionalExpression"):
                    return 1
                return None
            count = literal_extent(allocation)
            return count if count is not None and 0 < count <= 1024 else None
        initializer = getattr(allocation, "initExpr", None)
        if initializer is not None:
            # A fresh dynamic array may be initialized from an exact
            # positional assignment pattern.  Its sampled extent is the
            # allocation size; the assignment converter below expands the
            # scalar elements into the same flat cells used by a direct
            # dynamic-array pattern write.  Keep keyed/default, replicated,
            # aggregate, and effectful initializers outside this shape.
            while type(initializer).__name__ == "ConversionExpression":
                initializer = getattr(initializer, "operand", None)
                if initializer is None:
                    return None
            if type(initializer).__name__ in (
                    "SimpleAssignmentPatternExpression",
                    "StructuredAssignmentPatternExpression"):
                elements = _pattern_source_elements(initializer)
                size = getattr(allocation, "sizeExpr", None)
                if (not elements or type(size).__name__ != "IntegerLiteral"
                        or getattr(size, "bad", False)):
                    return None
                count = int(getattr(size, "value", -1))
                if count <= 0 or count > 1024 or len(elements) != count:
                    return None
                element_type = symbol.type.canonicalType.elementType
                if _dynamic_array_element_shape(element_type) is None:
                    return None
                if any(not _case_source_expression_ok(element,
                                                      packed_members=True)
                       for element in elements):
                    return None
                return count
            # A scalar dynamic array may be allocated from one other sampled
            # scalar dynamic array.  The copy itself is lowered at the
            # assignment site; this branch only exposes the fresh destination
            # extent to declaration/selection lowering.  Keep the source and
            # destination distinct so the later cell writes cannot overwrite
            # values that have not yet been copied.
            # Declaration-time initializers are converted by ``convert_var``;
            # this procedural assignment helper is the only place that emits
            # the source-cell copy, so do not expose an unmodelled declaration
            # copy as a sampled extent.
            if getattr(symbol, "initializer", None) is not None:
                return None
            source_expression = initializer
            while type(source_expression).__name__ == "ConversionExpression":
                source_expression = getattr(source_expression, "operand", None)
                if source_expression is None:
                    return None
            if type(source_expression).__name__ != "NamedValueExpression":
                return None
            source = getattr(source_expression, "symbol", None)
            if source is None or source is symbol:
                return None
            source_type = type(source.type.canonicalType).__name__
            if source_type == "DynamicArrayType":
                if _dynamic_array_constant_extent(source) is None:
                    return None
            elif source_type == "FixedSizeUnpackedArrayType":
                source_shape = _fixed_array_shape(source_expression)
                if source_shape is None:
                    return None
            else:
                return None
            source_element = source.type.canonicalType.elementType
            destination_element = symbol.type.canonicalType.elementType
            source_width, _source_two, source_reason = type_width_2s(source_element)
            destination_width, _destination_two, destination_reason = type_width_2s(
                destination_element)
            if (source_width is None or destination_width is None
                    or source_reason is not None or destination_reason is not None
                    or source_width != destination_width):
                return None
        size = getattr(allocation, "sizeExpr", None)
        if (type(size).__name__ != "IntegerLiteral"
                or getattr(size, "bad", False)):
            return None
        count = int(getattr(size, "value", -1))
        return count if 0 < count <= 1024 else None
    except Exception:
        return None


def _fixed_array_shape(source):
    """Return the lowered-cell shape for a one-dimensional fixed array."""
    try:
        # Assignment compatibility wraps an unpacked array RHS in a
        # ConversionExpression even though the value is still the same
        # storage.  Shape discovery is structural, so inspect its operand.
        if type(source).__name__ == "ConversionExpression":
            source = getattr(source, "operand", None)
            if source is None:
                return None
        if _storage_expression(source):
            source_name = _array_storage_name(source.symbol)
            source_type = source.type
            if str(source.symbol.kind) not in ("SymbolKind.Variable", "SymbolKind.Net"):
                return None
        else:
            path = _unpacked_struct_path(source)
            if path is None:
                return None
            source_name, source_type = path
            root = source
            while type(root).__name__ == "MemberAccessExpression":
                root = root.value
            if (not _storage_expression(root) or
                    str(root.symbol.kind) != "SymbolKind.Variable"):
                return None
        array_type = source_type.canonicalType
        array_kind = type(array_type).__name__
        if array_kind == "DynamicArrayType":
            # A dynamic array is representable by the flat state only when
            # its declaration samples a constant new[N] allocation.  The
            # allocation is then a fixed, zero-based window for this narrow
            # surface; later resize/assignment remains outside the model.
            # Four-state elements use the same flat cells, retaining their
            # x startup value; two-state elements keep their existing squash
            # rule.
            if not _storage_expression(source):
                return None
            count = _dynamic_array_constant_extent(source.symbol)
            if count is None:
                return None
            left, right = 0, count - 1
        elif array_kind == "FixedSizeUnpackedArrayType":
            left, right = int(array_type.range.left), int(array_type.range.right)
        else:
            return None
        element_type = array_type.elementType
        if type(element_type.canonicalType).__name__ == "FixedSizeUnpackedArrayType":
            return None
        width, two_state, reason = type_width_2s(element_type)
        if width is None or reason is not None:
            return None
        count = abs(left - right) + 1
        if count <= 0 or count > 1024:
            return None
        return source_name, width, two_state, left, right
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


def _fixed_array_subarray_shape(source):
    """Return the flattened cells of a constant fixed-array subarray.

    A selection that omits one or more rightmost unpacked dimensions is an
    unpacked subarray value (for example ``A[1]`` for ``int A[2][3]``).  The
    flat self-check state has no aggregate slot, so retain only the complete
    constant prefix and enumerate the remaining dimensions in declaration
    order.  Fully selected leaves and dynamic selections are handled by the
    ordinary element-select path and are deliberately not accepted here.
    """
    try:
        if type(source).__name__ != "ElementSelectExpression":
            return None
        selectors = []
        current = source
        while type(current).__name__ == "ElementSelectExpression":
            position = _constant_dimension_selector(current.selector)
            if position is None:
                return None
            selectors.append(position)
            current = current.value
        if not _storage_expression(current):
            return None
        if str(current.symbol.kind) != "SymbolKind.Variable":
            return None
        shape = _fixed_array_dimensions(current.type)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        if not selectors or len(selectors) >= len(dimensions):
            return None
        prefix_positions = list(reversed(selectors))
        for position, (left, right) in zip(prefix_positions, dimensions):
            if position < min(left, right) or position > max(left, right):
                return None
        width, two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None:
            return None
        remaining = dimensions[len(prefix_positions):]
        positions = [()]
        for left, right in remaining:
            step = 1 if right >= left else -1
            positions = [prefix + (position,)
                         for prefix in positions
                         for position in range(left, right + step, step)]
        if not positions or len(positions) > 1024:
            return None
        root_name = _array_storage_name(current.symbol)
        prefix_name = root_name + "".join(
            f"[{position}]" for position in prefix_positions)
        cells = [prefix_name + "".join(f"[{position}]" for position in suffix)
                 for suffix in positions]
        return root_name, cells, width, two_state
    except Exception:
        return None


def _fixed_array_subarray_copy_assignment(sm, expr):
    """Copy a selected fixed-array row into a flat fixed-array destination.

    SystemVerilog permits omitting trailing unpacked indices when selecting a
    subarray.  Once both arrays are represented as independent vector cells,
    a constant source prefix can be copied cellwise.  Reject destination/source
    aliasing because a sequential expansion would otherwise observe an earlier
    write, and require the source selection to be a pure expression.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None):
            return None
        lhs_subarray = _fixed_array_subarray_shape(expr.left)
        lhs_shape = (_fixed_array_assignment_shape(expr.left)
                     if lhs_subarray is None else None)
        rhs_shape = _fixed_array_subarray_shape(expr.right)
        rhs_array = _fixed_array_assignment_shape(expr.right)
        rhs_source = expr.right
        while type(rhs_source).__name__ == "ConversionExpression":
            rhs_source = getattr(rhs_source, "operand", None)
            if rhs_source is None:
                return None
        rhs_is_net = (str(getattr(getattr(rhs_source, "symbol", None), "kind", ""))
                      == "SymbolKind.Net")
        if lhs_subarray is not None and rhs_shape is None and rhs_array is not None:
            lhs_root, lhs_cells, lhs_width, lhs_two = lhs_subarray
            rhs_root, rhs_width, _rhs_two, rhs_positions = rhs_array
            rhs_cells = [f"{rhs_root}[{position}]" for position in rhs_positions]
            # A same-root copy is safe when the selected cell sets are
            # disjoint: each RHS read then precedes no write to that cell.
            # Overlap remains loud because a blocking expansion would expose
            # an earlier destination write to a later source read.
            aliasing = (lhs_root == rhs_root
                        and bool(set(lhs_cells) & set(rhs_cells)))
            if (len(lhs_cells) != len(rhs_positions) or lhs_width != rhs_width
                    or aliasing or not _case_source_expression_ok(expr.right)):
                return None
            stmts = []
            for lhs_name, rhs_name in zip(lhs_cells, rhs_cells):
                value = {
                    "kind": "Ident",
                    "span": node_span(sm, expr.right),
                    "width": rhs_width,
                    "name": rhs_name,
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
                        "name": lhs_name,
                    },
                    "value": value,
                })
            return {"kind": "Block", "span": node_span(sm, expr),
                    "stmts": stmts,
                    "fixed_array_subarray_copy_lowered": True}
        if lhs_shape is not None and rhs_shape is None and rhs_array is not None:
            lhs_name, lhs_width, lhs_two, lhs_positions = lhs_shape
            rhs_root, rhs_width, _rhs_two, rhs_positions = rhs_array
            lhs_cells = {f"{lhs_name}[{position}]" for position in lhs_positions}
            rhs_cells = [f"{rhs_root}[{position}]" for position in rhs_positions]
            aliasing = (lhs_name == rhs_root and bool(lhs_cells & set(rhs_cells)))
            if (len(lhs_positions) != len(rhs_cells) or lhs_width != rhs_width
                    or aliasing or not _case_source_expression_ok(expr.right)):
                return None
            stmts = []
            for lhs_position, rhs_name in zip(lhs_positions, rhs_cells):
                value = {"kind": "Ident", "span": node_span(sm, expr.right),
                         "width": rhs_width, "name": rhs_name}
                if lhs_two:
                    value = squash2_wrap(value, lhs_width)
                stmts.append({
                    "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                    "span": node_span(sm, expr),
                    "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                               "width": lhs_width,
                               "name": f"{lhs_name}[{lhs_position}]"},
                    "value": value,
                })
            result = {"kind": "Block", "span": node_span(sm, expr),
                      "stmts": stmts,
                      "fixed_array_slice_copy_lowered": True}
            if rhs_is_net:
                result["fixed_array_net_copy_lowered"] = True
            return result
        if lhs_shape is not None and rhs_shape is not None and rhs_array is None:
            lhs_name, lhs_width, lhs_two, lhs_positions = lhs_shape
            rhs_root, rhs_cells, rhs_width, _rhs_two = rhs_shape
            lhs_cells = [f"{lhs_name}[{position}]" for position in lhs_positions]
            aliasing = (lhs_name == rhs_root
                        and bool(set(lhs_cells) & set(rhs_cells)))
            if (len(lhs_cells) != len(rhs_cells) or lhs_width != rhs_width
                    or aliasing or not _case_source_expression_ok(expr.right)):
                return None
            stmts = []
            for lhs_name_cell, rhs_name in zip(lhs_cells, rhs_cells):
                value = {"kind": "Ident", "span": node_span(sm, expr.right),
                         "width": rhs_width, "name": rhs_name}
                if lhs_two:
                    value = squash2_wrap(value, lhs_width)
                stmts.append({
                    "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                    "span": node_span(sm, expr),
                    "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                               "width": lhs_width, "name": lhs_name_cell},
                    "value": value,
                })
            return {"kind": "Block", "span": node_span(sm, expr),
                    "stmts": stmts,
                    "fixed_array_subarray_copy_lowered": True}
        if lhs_shape is None or rhs_shape is None:
            return None
        lhs_name, lhs_width, lhs_two, lhs_positions = lhs_shape
        rhs_root, rhs_cells, rhs_width, _rhs_two = rhs_shape
        lhs_cells = {f"{lhs_name}[{position}]" for position in lhs_positions}
        aliasing = (lhs_name == rhs_root and bool(lhs_cells & set(rhs_cells)))
        if (len(lhs_positions) != len(rhs_cells) or lhs_width != rhs_width
                or aliasing):
            return None
        if not _case_source_expression_ok(expr.right):
            return None
        stmts = []
        for lhs_position, rhs_name in zip(lhs_positions, rhs_cells):
            value = {
                "kind": "Ident",
                "span": node_span(sm, expr.right),
                "width": rhs_width,
                "name": rhs_name,
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
        return {"kind": "Block", "span": node_span(sm, expr),
                "stmts": stmts, "fixed_array_subarray_copy_lowered": True}
    except Exception:
        return None


def _fixed_array_dynamic_subarray_copy_assignment(sm, expr):
    """Copy a flat fixed-array row into one dynamic multidimensional prefix.

    A dynamic prefix selection such as ``matrix[i] = row`` has no aggregate
    slot in the flat self-check state.  For a bounded multidimensional array,
    expand the selected prefix into mutually exclusive branches over the
    finite dynamic dimension, then copy each suffix cell in declaration order.
    The source is required to be a distinct, constant-shape flat array so a
    blocking expansion cannot observe an earlier destination write.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None
                or type(expr.left).__name__ != "ElementSelectExpression"):
            return None
        lhs = expr.left
        selectors = []
        current = lhs
        while type(current).__name__ == "ElementSelectExpression":
            selectors.append(current.selector)
            current = current.value
        # A constant selector is already handled by the ordinary subarray
        # copy; this item admits exactly one dynamic selector in the selected
        # prefix and leaves at least one suffix dimension omitted.
        if not selectors or not _storage_expression(current):
            return None
        if str(current.symbol.kind) != "SymbolKind.Variable":
            return None
        shape = _fixed_array_dimensions(current.type, max_cells=1024)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        prefix_positions = list(reversed(selectors))
        if not (0 < len(prefix_positions) < len(dimensions)):
            return None
        dynamic = [index for index, item in enumerate(prefix_positions)
                   if _constant_dimension_selector(item) is None]
        if len(dynamic) != 1:
            return None
        dynamic_index = dynamic[0]
        selector = prefix_positions[dynamic_index]
        width, two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None:
            return None
        index_width, _index_two, index_reason = type_width_2s(selector.type)
        if (index_width is None or index_reason is not None
                or not _case_source_expression_ok(selector)
                or not _case_source_expression_ok(expr.right)):
            return None
        converted_index = convert_expr(sm, selector)
        if (converted_index is None or not _case_expression_ok(converted_index)
                or width_of(converted_index) != index_width):
            return None

        rhs_shape = _fixed_array_assignment_shape(expr.right)
        if rhs_shape is None:
            return None
        rhs_root, rhs_width, _rhs_two, rhs_positions = rhs_shape
        fixed_prefix = []
        for index, (selector_value, (left, right)) in enumerate(
                zip(prefix_positions, dimensions)):
            if index == dynamic_index:
                fixed_prefix.append(None)
                continue
            position = _constant_dimension_selector(selector_value)
            if position is None or position < min(left, right) or position > max(left, right):
                return None
            fixed_prefix.append(position)

        suffix = dimensions[len(prefix_positions):]
        suffix_positions = [()]
        for left, right in suffix:
            step = 1 if right >= left else -1
            suffix_positions = [prefix + (position,)
                                for prefix in suffix_positions
                                for position in range(left, right + step, step)]
        if (not suffix_positions or len(suffix_positions) > 1024
                or len(rhs_positions) != len(suffix_positions)
                or rhs_width != width):
            return None

        root_name = _array_storage_name(current.symbol)
        rhs_cells = [f"{rhs_root}[{position}]" for position in rhs_positions]
        destination_cells = []
        dynamic_left, dynamic_right = dimensions[dynamic_index]
        dynamic_step = 1 if dynamic_right >= dynamic_left else -1
        for outer in range(dynamic_left, dynamic_right + dynamic_step, dynamic_step):
            indexes = list(fixed_prefix)
            indexes[dynamic_index] = outer
            destination_cells.extend(
                root_name + "".join(f"[{position}]" for position in indexes)
                + "".join(f"[{position}]" for position in suffix)
                for suffix in suffix_positions)
        # A same-root source may overlap one of the possible rows; reject it
        # rather than changing the source snapshot through blocking writes.
        if rhs_root == root_name and set(destination_cells) & set(rhs_cells):
            return None

        mask = (1 << index_width) - 1
        result = None
        for outer in reversed(list(range(dynamic_left, dynamic_right + dynamic_step,
                                        dynamic_step))):
            indexes = list(fixed_prefix)
            indexes[dynamic_index] = outer
            stmts = []
            for target_name, rhs_name in zip(
                    [root_name + "".join(f"[{position}]" for position in indexes)
                     + "".join(f"[{position}]" for position in suffix)
                     for suffix in suffix_positions],
                    rhs_cells):
                value = {"kind": "Ident", "span": node_span(sm, expr.right),
                         "width": rhs_width, "name": rhs_name}
                if two_state:
                    value = squash2_wrap(value, width)
                stmts.append({
                    "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                    "span": node_span(sm, expr),
                    "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                               "width": width, "name": target_name},
                    "value": value,
                })
            branch = {"kind": "Block", "span": node_span(sm, expr),
                      "stmts": stmts}
            literal = {"kind": "Literal", "span": node_span(sm, selector),
                       "width": index_width,
                       "bits": format(outer & mask, f"0{index_width}b")}
            result = {"kind": "If", "span": node_span(sm, expr),
                      "cond": {"kind": "Binary", "span": node_span(sm, selector),
                               "width": 1, "op": "===", "left": converted_index,
                               "right": literal},
                      "then": branch, "else": result}
        if result is not None:
            result["fixed_array_dynamic_subarray_copy_lowered"] = True
        return result
    except Exception:
        return None


def _fixed_array_dynamic_subarray_read_copy_assignment(sm, expr):
    """Copy one dynamic multidimensional prefix into a flat fixed array."""
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None):
            return None
        lhs_shape = _fixed_array_assignment_shape(expr.left)
        if lhs_shape is None:
            return None
        lhs_name, lhs_width, lhs_two, lhs_positions = lhs_shape
        selectors = []
        current = expr.right
        while type(current).__name__ == "ElementSelectExpression":
            selectors.append(current.selector)
            current = current.value
        if not selectors or not _storage_expression(current):
            return None
        if str(current.symbol.kind) != "SymbolKind.Variable":
            return None
        shape = _fixed_array_dimensions(current.type, max_cells=1024)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        prefix_positions = list(reversed(selectors))
        if not (0 < len(prefix_positions) < len(dimensions)):
            return None
        dynamic = [index for index, item in enumerate(prefix_positions)
                   if _constant_dimension_selector(item) is None]
        if len(dynamic) != 1:
            return None
        dynamic_index = dynamic[0]
        selector = prefix_positions[dynamic_index]
        width, _two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None:
            return None
        index_width, _index_two, index_reason = type_width_2s(selector.type)
        if (index_width is None or index_reason is not None
                or not _case_source_expression_ok(selector)
                or not _case_source_expression_ok(expr.right)):
            return None
        converted_index = convert_expr(sm, selector)
        if (converted_index is None or not _case_expression_ok(converted_index)
                or width_of(converted_index) != index_width):
            return None

        fixed_prefix = []
        for index, (selector_value, (left, right)) in enumerate(
                zip(prefix_positions, dimensions)):
            if index == dynamic_index:
                fixed_prefix.append(None)
                continue
            position = _constant_dimension_selector(selector_value)
            if position is None or position < min(left, right) or position > max(left, right):
                return None
            fixed_prefix.append(position)
        suffix = dimensions[len(prefix_positions):]
        suffix_positions = [()]
        for left, right in suffix:
            step = 1 if right >= left else -1
            suffix_positions = [prefix + (position,)
                                for prefix in suffix_positions
                                for position in range(left, right + step, step)]
        if (not suffix_positions or len(suffix_positions) > 1024
                or len(lhs_positions) != len(suffix_positions)
                or lhs_width != width or not _case_source_expression_ok(expr.right)):
            return None

        root_name = _array_storage_name(current.symbol)
        lhs_cells = [f"{lhs_name}[{position}]" for position in lhs_positions]
        dynamic_left, dynamic_right = dimensions[dynamic_index]
        dynamic_step = 1 if dynamic_right >= dynamic_left else -1
        source_cells = []
        for outer in range(dynamic_left, dynamic_right + dynamic_step, dynamic_step):
            indexes = list(fixed_prefix)
            indexes[dynamic_index] = outer
            source_cells.extend(
                root_name + "".join(f"[{position}]" for position in indexes)
                + "".join(f"[{position}]" for position in suffix)
                for suffix in suffix_positions)
        if lhs_name == root_name and set(lhs_cells) & set(source_cells):
            return None

        mask = (1 << index_width) - 1
        result = None
        for outer in reversed(list(range(dynamic_left, dynamic_right + dynamic_step,
                                        dynamic_step))):
            indexes = list(fixed_prefix)
            indexes[dynamic_index] = outer
            branch_sources = [
                root_name + "".join(f"[{position}]" for position in indexes)
                + "".join(f"[{position}]" for position in suffix)
                for suffix in suffix_positions]
            stmts = []
            for lhs_cell, source_name in zip(lhs_cells, branch_sources):
                value = {"kind": "Ident", "span": node_span(sm, expr.right),
                         "width": width, "name": source_name}
                if lhs_two:
                    value = squash2_wrap(value, lhs_width)
                stmts.append({
                    "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                    "span": node_span(sm, expr),
                    "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                               "width": lhs_width, "name": lhs_cell},
                    "value": value,
                })
            literal = {"kind": "Literal", "span": node_span(sm, selector),
                       "width": index_width,
                       "bits": format(outer & mask, f"0{index_width}b")}
            result = {"kind": "If", "span": node_span(sm, expr),
                      "cond": {"kind": "Binary", "span": node_span(sm, selector),
                               "width": 1, "op": "===", "left": converted_index,
                               "right": literal},
                      "then": {"kind": "Block", "span": node_span(sm, expr),
                               "stmts": stmts},
                      "else": result}
        if result is not None:
            result["fixed_array_dynamic_subarray_read_copy_lowered"] = True
        return result
    except Exception:
        return None


def _fixed_array_subarray_pattern_assignment(sm, expr):
    """Lower an exact pattern assigned to a constant array subarray."""
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None):
            return None
        lhs_shape = _fixed_array_subarray_shape(expr.left)
        if lhs_shape is None:
            return None
        root_name, cells, width, two_state = lhs_shape
        pattern_kind = type(expr.right).__name__
        if pattern_kind not in ("SimpleAssignmentPatternExpression",
                                "StructuredAssignmentPatternExpression",
                                "ReplicatedAssignmentPatternExpression"):
            return None
        dimensions_shape = _fixed_array_dimensions(expr.left.type)
        if dimensions_shape is None:
            return None
        dimensions, leaf_type = dimensions_shape
        if type(leaf_type).__name__ in ("FixedSizeUnpackedArrayType",
                                        "UnpackedStructType", "UnpackedUnionType",
                                        "DynamicArrayType", "QueueType",
                                        "AssociativeArrayType"):
            return None
        elements = _fixed_array_pattern_elements(expr.right, dimensions)
        if elements is None or len(elements) != len(cells):
            return None
        values = []
        for element in elements:
            if not _case_source_expression_ok(element, packed_members=True):
                return None
            reads_root = False

            def inspect(node):
                nonlocal reads_root
                if type(node).__name__ in ("NamedValueExpression",
                                            "HierarchicalValueExpression"):
                    try:
                        reads_root = reads_root or _array_storage_name(node.symbol) == root_name
                    except Exception:
                        reads_root = True

            _visit_selected_expression(element, inspect)
            if reads_root:
                return None
            value = convert_expr(sm, element)
            if (value is None or value.get("kind") == "Unsupported"
                    or width_of(value) != width or not _case_expression_ok(value)):
                return None
            values.append(squash2_wrap(value, width) if two_state else value)
        stmts = []
        for cell, value in zip(cells, values):
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                           "width": width, "name": cell},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr),
                "stmts": stmts, "fixed_array_subarray_pattern_lowered": True}
    except Exception:
        return None


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


def _fixed_array_nested_dynamic_read(sm, expression):
    """Read a finite multidimensional array with one innermost dynamic index."""
    try:
        if type(expression).__name__ != "ElementSelectExpression":
            return None
        selectors = []
        current = expression
        while type(current).__name__ == "ElementSelectExpression":
            selectors.append(current.selector)
            current = current.value
        if not _storage_expression(current):
            return None
        shape = _fixed_array_dimensions(current.type, max_cells=1024)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        if len(selectors) != len(dimensions):
            return None
        positions = list(reversed(selectors))
        dynamic = [i for i, selector in enumerate(positions)
                   if _constant_dimension_selector(selector) is None]
        if len(dynamic) != 1:
            return None
        dynamic_index = dynamic[0]
        width, two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None:
            return None
        fixed = []
        for index, (selector, (left, right)) in enumerate(zip(positions, dimensions)):
            if index == dynamic_index:
                fixed.append(None)
                continue
            value = _constant_dimension_selector(selector)
            if value is None or value < min(left, right) or value > max(left, right):
                return None
            fixed.append(value)
        selector = positions[dynamic_index]
        index_width, _index_two, index_reason = type_width_2s(selector.type)
        if (index_width is None or index_reason is not None
                or not _case_source_expression_ok(selector)):
            return None
        converted_index = convert_expr(sm, selector)
        if converted_index is None or width_of(converted_index) != index_width:
            return None
        left, right = dimensions[dynamic_index]
        result = {"kind": "Literal", "span": node_span(sm, expression),
                  "width": width, "bits": "0" if two_state else "x" * width}
        if two_state:
            result["bits"] = "0" * width
        mask = (1 << index_width) - 1
        step = 1 if right >= left else -1
        root = _array_storage_name(current.symbol)
        for position in reversed(list(range(left, right + step, step))):
            indexes = list(fixed)
            indexes[dynamic_index] = position
            name = root + "".join(f"[{item}]" for item in indexes)
            literal = {"kind": "Literal", "span": node_span(sm, selector),
                       "width": index_width,
                       "bits": format(position & mask, f"0{index_width}b")}
            result = {"kind": "Ternary", "span": node_span(sm, expression),
                      "width": width,
                      "cond": {"kind": "Binary", "span": node_span(sm, selector),
                               "width": 1, "op": "===", "left": converted_index,
                               "right": literal},
                      "then": {"kind": "Ident", "span": node_span(sm, expression),
                               "width": width, "name": name},
                      "else": result}
        return result
    except Exception:
        return None


def _dist_uniform_fixed_array_assignment(sm, expr):
    """Lower a bounded ``$dist_uniform`` write to flat array cells.

    ``$dist_uniform`` is an inout system function: it advances its 32-bit
    integer seed and returns a bounded integer.  The self-check state has no
    aggregate slot, but a finite fixed array is already expanded into cells,
    so the dynamic index can use the same guarded lowering as ordinary array
    writes.  Keep the first admitted random family deliberately narrow: a
    direct variable seed, literal bounds ``0`` and ``1000``, and an integral
    one-dimensional fixed array destination.  Other random calls remain loud.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None
                or type(expr.left).__name__ != "ElementSelectExpression"
                ):
            return None
        call = expr.right
        while type(call).__name__ == "ConversionExpression":
            call = getattr(call, "operand", None)
            if call is None:
                return None
        if (type(call).__name__ != "CallExpression"
                or not call.isSystemCall
                or call.subroutineName != "$dist_uniform"):
            return None
        args = list(call.arguments)
        if len(args) != 3:
            return None
        seed_arg = args[0]
        if (type(seed_arg).__name__ != "AssignmentExpression"
                or seed_arg.op is not None
                or type(seed_arg.left).__name__ != "NamedValueExpression"
                or type(seed_arg.right).__name__ != "EmptyArgumentExpression"):
            return None
        seed_symbol = getattr(seed_arg.left, "symbol", None)
        if (seed_symbol is None or str(getattr(seed_symbol, "kind", ""))
                != "SymbolKind.Variable"):
            return None
        seed_width, _seed_two, seed_reason = type_width_2s(seed_arg.left.type)
        if seed_width != 32 or seed_reason is not None:
            return None
        low = _literal_integral_value(args[1])
        high = _literal_integral_value(args[2])
        if low != 0 or high != 1000:
            return None
        shape = _fixed_array_shape(expr.left.value)
        if shape is None:
            return None
        name, width, two_state, left, right = shape
        index = expr.left.selector
        if _constant_dimension_selector(index) is not None:
            return None
        index_width, _index_two, index_reason = type_width_2s(index.type)
        if (index_width is None or index_reason is not None
                or not _case_source_expression_ok(index)):
            return None
        converted_index = convert_expr(sm, index)
        if (converted_index is None or not _case_expression_ok(converted_index)
                or width_of(converted_index) != index_width
                or width != expr.right.type.bitWidth):
            return None
        seed_name = _storage_name(seed_symbol)
        result = None
        step = 1 if right >= left else -1
        mask = (1 << index_width) - 1
        for position in reversed(list(range(left, right + step, step))):
            literal = {
                "kind": "Literal", "span": node_span(sm, index),
                "width": index_width,
                "bits": format(position & mask, f"0{index_width}b"),
            }
            branch = {
                "kind": "DistUniformAssign",
                "span": node_span(sm, expr),
                "target": f"{name}[{position}]",
                "seed": seed_name,
                "low": low,
                "high": high,
                "two_state": two_state,
            }
            result = {
                "kind": "If", "span": node_span(sm, expr),
                "cond": {
                    "kind": "Binary", "span": node_span(sm, index),
                    "width": 1, "op": "===", "left": converted_index,
                    "right": literal,
                },
                "then": branch, "else": result,
            }
        if result is not None:
            result["dist_uniform_array_write_lowered"] = True
        return result
    except Exception:
        return None


def _dist_uniform_scalar_assignment(sm, expr):
    """Lower a literal signed ``$dist_uniform`` call into one cell.

    The inout seed and the returned value are represented by the same
    ``DistUniformAssign`` statement used for fixed-array cells.  Keep this
    first scalar rung deliberately narrow: a direct 32-bit variable seed,
    literal bounds in the signed 32-bit range, and a direct
    32-bit integral target.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None or expr.isNonBlocking
                or type(expr.left).__name__ != "NamedValueExpression"):
            return None
        target_symbol = getattr(expr.left, "symbol", None)
        if (target_symbol is None
                or str(getattr(target_symbol, "kind", ""))
                != "SymbolKind.Variable"):
            return None
        target_width, target_two_state, target_reason = type_width_2s(
            expr.left.type)
        if target_width != 32 or target_reason is not None:
            return None
        call = expr.right
        while type(call).__name__ == "ConversionExpression":
            call = getattr(call, "operand", None)
            if call is None:
                return None
        if (type(call).__name__ != "CallExpression"
                or not call.isSystemCall
                or call.subroutineName != "$dist_uniform"):
            return None
        args = list(call.arguments)
        if len(args) != 3:
            return None
        seed_arg = args[0]
        if (type(seed_arg).__name__ != "AssignmentExpression"
                or seed_arg.op is not None
                or type(seed_arg.left).__name__ != "NamedValueExpression"
                or type(seed_arg.right).__name__ != "EmptyArgumentExpression"):
            return None
        seed_symbol = getattr(seed_arg.left, "symbol", None)
        if (seed_symbol is None
                or str(getattr(seed_symbol, "kind", ""))
                != "SymbolKind.Variable"):
            return None
        seed_width, _seed_two_state, seed_reason = type_width_2s(
            seed_arg.left.type)
        if seed_width != 32 or seed_reason is not None:
            return None
        low = _literal_integral_value(args[1])
        high = _literal_integral_value(args[2])
        if (low is None or high is None or high < low
                or low < -(1 << 31) or high > (1 << 31) - 1):
            return None
        return {
            "kind": "DistUniformAssign",
            "span": node_span(sm, expr),
            "target": _storage_name(target_symbol),
            "seed": _storage_name(seed_symbol),
            "low": low,
            "high": high,
            "two_state": target_two_state,
            "dist_uniform_scalar_write": True,
        }
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
        # A post-increment/decrement selector has a pure index value and a
        # separate lvalue update.  Preserve the source order by selecting the
        # old index, then committing the update after the conditional write.
        # Pre-increment remains outside this narrow lowering because its
        # update must occur before the selector is sampled.
        index_update = None
        if type(index).__name__ == "UnaryExpression":
            index_op = str(getattr(index, "op", None)).split(".")[-1]
            if index_op not in ("Postincrement", "Postdecrement"):
                return None
            index_update = _convert_incdec(sm, index, "AssignmentExpression:index")
            if (index_update is None
                    or index_update.get("kind") == "Unsupported"):
                return None
            index = index.operand
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
        if index_update is not None:
            return {"kind": "Block", "span": node_span(sm, expr),
                    "stmts": [result, index_update],
                    "postindexed_array_write_lowered": True}
        return result
    except Exception:
        return None


def _fixed_array_nested_dynamic_assignment(sm, expr):
    """Lower one dynamic selector through a finite multidimensional array.

    Every other unpacked dimension must be selected by a constant label. The
    finite cell expansion then becomes a mutually exclusive conditional over
    the one dynamic dimension; multiple dynamic selectors and aggregate leaves
    stay on the ordinary loud target boundary.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None
                or type(expr.left).__name__ != "ElementSelectExpression"):
            return None
        selectors = []
        current = expr.left
        while type(current).__name__ == "ElementSelectExpression":
            selectors.append(current.selector)
            current = current.value
        if not _storage_expression(current):
            return None
        shape = _fixed_array_dimensions(current.type, max_cells=1024)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        if len(selectors) != len(dimensions):
            return None
        positions = list(reversed(selectors))
        dynamic = [index for index, selector in enumerate(positions)
                   if _constant_dimension_selector(selector) is None]
        if len(dynamic) != 1:
            return None
        dynamic_index = dynamic[0]
        width, two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None:
            return None
        selector = positions[dynamic_index]
        index_width, _index_two, index_reason = type_width_2s(selector.type)
        if (index_width is None or index_reason is not None
                or not _case_source_expression_ok(selector)
                or not _case_source_expression_ok(expr.right)):
            return None
        converted_index = convert_expr(sm, selector)
        value = convert_expr(sm, expr.right)
        if (converted_index is None or value is None
                or width_of(converted_index) != index_width
                or width_of(value) != width
                or not _case_expression_ok(converted_index)
                or not _case_expression_ok(value)):
            return None
        fixed_positions = []
        for index, (selector_value, (left, right)) in enumerate(zip(positions, dimensions)):
            if index == dynamic_index:
                fixed_positions.append(None)
                continue
            position = _constant_dimension_selector(selector_value)
            if position is None or position < min(left, right) or position > max(left, right):
                return None
            fixed_positions.append(position)
        left, right = dimensions[dynamic_index]
        step = 1 if right >= left else -1
        mask = (1 << index_width) - 1
        result = None
        for position in reversed(list(range(left, right + step, step))):
            indexes = list(fixed_positions)
            indexes[dynamic_index] = position
            name = _array_storage_name(current.symbol) + "".join(
                f"[{item}]" for item in indexes)
            branch_value = squash2_wrap(value, width) if two_state else value
            branch = {"kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                      "span": node_span(sm, expr),
                      "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                                 "width": width, "name": name},
                      "value": branch_value}
            literal = {"kind": "Literal", "span": node_span(sm, selector),
                       "width": index_width,
                       "bits": format(position & mask, f"0{index_width}b")}
            result = {"kind": "If", "span": node_span(sm, expr),
                      "cond": {"kind": "Binary", "span": node_span(sm, selector),
                               "width": 1, "op": "===", "left": converted_index,
                               "right": literal},
                      "then": branch, "else": result}
        return result
    except Exception:
        return None


def _dynamic_array_allocation_assignment(sm, expr):
    """Erase a sampled constant ``dynamic = new[N]`` allocation.

    The declaration pass materializes the allocated cells after checking the
    complete module's single allocation.  The procedural allocation then
    has no separate flat-state effect; nonconstant and repeated allocations
    remain ordinary assignment-target refusals.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None
                or type(expr.left).__name__ != "NamedValueExpression"):
            return None
        symbol = getattr(expr.left, "symbol", None)
        if symbol is None or type(symbol.type.canonicalType).__name__ != "DynamicArrayType":
            return None
        allocation = expr.right
        if type(allocation).__name__ == "ConversionExpression":
            allocation = getattr(allocation, "operand", None)
        if type(allocation).__name__ != "NewArrayExpression":
            return None
        if getattr(allocation, "initExpr", None) is not None:
            return None
        size = getattr(allocation, "sizeExpr", None)
        if type(size).__name__ != "IntegerLiteral" or getattr(size, "bad", False):
            return None
        if getattr(size, "value", None) == 0:
            return {"kind": "Empty", "span": node_span(sm, expr),
                    "empty_dynamic_array_allocation_noop": True}
        if _dynamic_array_constant_extent(symbol) is None:
            return None
        # A second ``new[N]`` without an initializer destroys the previous
        # dynamic-array value and creates fresh default cells.  The flat
        # representation keeps the same names for those cells, so publish
        # the new defaults explicitly at the reinitialization boundary.
        # Resize-copy (``new[N](old)``), self-growth, and every third
        # allocation remain on their existing loud paths.
        instance = symbol.parentScope.containingInstance
        allocations = []
        if instance is not None:
            def inspect(node):
                if (type(node).__name__ == "AssignmentExpression"
                        and getattr(getattr(node, "left", None), "symbol", None)
                        is symbol):
                    allocations.append(node)
            instance.visit(inspect)
        if (len(allocations) == 2 and allocations[1] is expr
                and getattr(allocations[0].right, "initExpr", None) is None):
            first = allocations[0].right
            while type(first).__name__ == "ConversionExpression":
                first = getattr(first, "operand", None)
            first_size = getattr(first, "sizeExpr", None)
            if (type(first).__name__ == "NewArrayExpression"
                    and type(first_size).__name__ == "IntegerLiteral"
                    and not getattr(first_size, "bad", False)
                    and getattr(first_size, "value", 0) > 0):
                element = symbol.type.canonicalType.elementType
                width, two_state, reason = type_width_2s(element)
                count = int(getattr(size, "value", -1))
                if (width is not None and reason is None and 0 < count <= 1024):
                    base = _array_storage_name(symbol)
                    default_bits = ("0" if two_state else "x") * width
                    span = node_span(sm, expr)
                    return {
                        "kind": "Block",
                        "span": span,
                        "stmts": [{
                            "kind": "BlockingAssign",
                            "span": span,
                            "target": {
                                "kind": "Ident",
                                "span": node_span(sm, expr.left),
                                "width": width,
                                "name": f"{base}[{index}]",
                            },
                            "value": {
                                "kind": "Literal",
                                "span": span,
                                "width": width,
                                "bits": default_bits,
                            },
                        } for index in range(count)],
                        "dynamic_array_reinitialization_lowered": True,
                    }
        return {"kind": "Empty", "span": node_span(sm, expr),
                "dynamic_array_allocation_lowered": True}
    except Exception:
        return None


def _dynamic_array_resize_copy_assignment(sm, expr):
    """Lower ``dst = new[N](src)`` for sampled scalar arrays.

    A dynamic array has no aggregate slot in the flat self-check state, but a
    fresh constant-size array does have one independent cell per element.  For
    two distinct sampled scalar arrays, the IEEE copy is therefore a block of
    ordinary cell writes followed by the destination's default padding.  A
    self-copy, dynamic size, aggregate element, nested array, or source type
    mismatch stays on the ordinary target boundary.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None or expr.isNonBlocking
                or type(expr.left).__name__ != "NamedValueExpression"):
            return None
        destination = getattr(expr.left, "symbol", None)
        if (destination is None
                or type(destination.type.canonicalType).__name__ != "DynamicArrayType"):
            return None
        allocation = expr.right
        if type(allocation).__name__ == "ConversionExpression":
            allocation = getattr(allocation, "operand", None)
        if type(allocation).__name__ != "NewArrayExpression":
            return None
        initializer = getattr(allocation, "initExpr", None)
        source_expression = initializer
        while type(source_expression).__name__ == "ConversionExpression":
            source_expression = getattr(source_expression, "operand", None)
            if source_expression is None:
                return None
        if type(source_expression).__name__ != "NamedValueExpression":
            return None
        source = getattr(source_expression, "symbol", None)
        self_resize = source is destination
        if source is None:
            return None
        source_type = type(source.type.canonicalType).__name__
        if source_type not in ("DynamicArrayType", "FixedSizeUnpackedArrayType"):
            return None
        size = getattr(allocation, "sizeExpr", None)
        if type(size).__name__ != "IntegerLiteral" or getattr(size, "bad", False):
            return None
        destination_count = int(getattr(size, "value", -1))
        if destination_count <= 0 or destination_count > 1024:
            return None
        source_shape = _fixed_array_shape(source_expression)
        if source_shape is None:
            return None
        source_base, source_width, source_two, source_left, source_right = source_shape
        source_positions = list(range(
            source_left, source_right + (1 if source_right >= source_left else -1),
            1 if source_right >= source_left else -1))
        source_count = len(source_positions)
        if self_resize:
            # The destination shape includes the new cells. Only the cells
            # from the preceding allocation are source values, and growth is
            # the sole admitted self-resize direction.
            if source_type != "DynamicArrayType":
                return None
            instance = destination.parentScope.containingInstance
            allocations = []
            def inspect(node):
                if (type(node).__name__ == "AssignmentExpression"
                        and getattr(getattr(node, "left", None), "symbol", None)
                        is destination):
                    allocations.append(node.right)
            instance.visit(inspect)
            if len(allocations) != 2:
                return None
            first = allocations[0]
            while type(first).__name__ == "ConversionExpression":
                first = getattr(first, "operand", None)
            if type(first).__name__ != "NewArrayExpression":
                return None
            first_size = getattr(first, "sizeExpr", None)
            if (type(first_size).__name__ != "IntegerLiteral"
                    or getattr(first_size, "bad", False)):
                return None
            old_count = int(getattr(first_size, "value", -1))
            if old_count <= 0 or old_count > source_count:
                return None
            source_positions = source_positions[:old_count]
            source_count = old_count
        destination_element = destination.type.canonicalType.elementType
        source_element = source.type.canonicalType.elementType
        destination_width, destination_two, destination_reason = type_width_2s(
            destination_element)
        source_width_check, _source_two, source_reason = type_width_2s(source_element)
        if (destination_width is None or source_width is None
                or destination_reason is not None or source_reason is not None
                or destination_width != source_width_check):
            return None
        destination_base = _array_storage_name(destination)
        span = node_span(sm, expr)
        prefix = []
        source_values = []
        if self_resize:
            for position in range(source_count):
                temporary = _scoped_temp("$resize:", expr.sourceRange.start.offset,
                                         ":%d" % position)
                source_values.append({"kind": "Ident", "span": None,
                                      "width": source_width, "name": temporary})
                prefix.append({"kind": "LocalDecl", "span": span,
                               "width": source_width, "name": temporary,
                               "two_state": False,
                               "init": {"kind": "Ident",
                                        "span": node_span(sm, initializer),
                                        "width": source_width,
                                        "name": f"{source_base}[{source_positions[position]}]"},
                               "automatic_resize": True})
        statements = []
        for position in range(destination_count):
            if position < source_count:
                value = {
                    "kind": "Ident", "span": node_span(sm, initializer),
                    "width": source_width,
                    "name": (source_values[position]["name"] if self_resize
                              else f"{source_base}[{source_positions[position]}]"),
                }
                if destination_two and source_element.isFourState:
                    value = squash2_wrap(value, destination_width)
            else:
                value = {
                    "kind": "Literal", "span": span,
                    "width": destination_width,
                    "bits": ("0" if destination_two else "x") * destination_width,
                }
            statements.append({
                "kind": "BlockingAssign", "span": span,
                "target": {
                    "kind": "Ident", "span": node_span(sm, expr.left),
                    "width": destination_width,
                    "name": f"{destination_base}[{position}]",
                },
                "value": value,
            })
        return {"kind": "Block", "span": span, "stmts": prefix + statements,
                "dynamic_array_resize_copy_lowered": True}
    except Exception:
        return None


def _dynamic_array_new_pattern_assignment(sm, expr):
    """Lower ``dst = new[N]('{scalar, ...})`` into flat array cells.

    The allocated array has no aggregate slot in the self-check state, so
    this admits only an exact positional pattern of scalar integral values.
    The size, element count, width, source effects, and destination shape are
    all checked before any cells are emitted; keyed/default, replicated,
    nested, effectful, nonblocking, and timed forms stay on the ordinary loud
    assignment boundary.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None or expr.isNonBlocking
                or type(expr.left).__name__ != "NamedValueExpression"):
            return None
        lhs = expr.left
        array_type = lhs.type.canonicalType
        if type(array_type).__name__ != "DynamicArrayType":
            return None
        allocation = expr.right
        while type(allocation).__name__ == "ConversionExpression":
            allocation = getattr(allocation, "operand", None)
            if allocation is None:
                return None
        if type(allocation).__name__ != "NewArrayExpression":
            return None
        size = getattr(allocation, "sizeExpr", None)
        if (type(size).__name__ != "IntegerLiteral"
                or getattr(size, "bad", False)):
            return None
        count = int(getattr(size, "value", -1))
        if count <= 0 or count > 1024:
            return None
        pattern = getattr(allocation, "initExpr", None)
        while type(pattern).__name__ == "ConversionExpression":
            pattern = getattr(pattern, "operand", None)
            if pattern is None:
                return None
        if type(pattern).__name__ not in (
                "SimpleAssignmentPatternExpression",
                "StructuredAssignmentPatternExpression"):
            return None
        elements = _pattern_source_elements(pattern)
        if not elements or len(elements) != count:
            return None
        if _dynamic_array_constant_extent(lhs.symbol) != count:
            return None
        element_type = array_type.elementType
        width, two_state, reason = type_width_2s(element_type)
        if width is None or reason is not None:
            return None
        base = _array_storage_name(lhs.symbol)
        values = []
        for element in elements:
            if not _case_source_expression_ok(element, packed_members=True):
                return None
            reads_target = False

            def inspect(node):
                nonlocal reads_target
                if type(node).__name__ in ("NamedValueExpression",
                                            "HierarchicalValueExpression"):
                    try:
                        reads_target = reads_target or (
                            _array_storage_name(node.symbol) == base)
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
            if two_state:
                value = squash2_wrap(value, width)
            values.append(value)
        span = node_span(sm, expr)
        return {"kind": "Block", "span": span, "stmts": [{
            "kind": "BlockingAssign", "span": span,
            "target": {"kind": "Ident", "span": node_span(sm, lhs),
                       "width": width, "name": f"{base}[{index}]"},
            "value": value,
        } for index, value in enumerate(values)],
                "dynamic_array_new_pattern_lowered": True}
    except Exception:
        return None


def _dynamic_array_pattern_assignment(sm, expr):
    """Lower an exact scalar assignment pattern into sampled array cells.

    A dynamic array has no aggregate slot in the self-check state, but a
    finite positional pattern samples a fixed length just like an unpacked
    concatenation.  Keep the lowering strict: scalar integral elements only,
    exact width, no destination reads, and no nonblocking/timed form.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None
                or type(expr.left).__name__ != "NamedValueExpression"):
            return None
        lhs = expr.left
        array_type = lhs.type.canonicalType
        if type(array_type).__name__ != "DynamicArrayType":
            return None
        pattern = expr.right
        if type(pattern).__name__ not in (
                "SimpleAssignmentPatternExpression",
                "StructuredAssignmentPatternExpression"):
            return None
        elements = _pattern_source_elements(pattern)
        if not elements or len(elements) != _dynamic_array_constant_extent(lhs.symbol):
            return None
        element_type = array_type.elementType
        width, two_state, reason = type_width_2s(element_type)
        if width is None or reason is not None:
            return None
        base = _array_storage_name(lhs.symbol)
        values = []
        for element in elements:
            if not _case_source_expression_ok(element, packed_members=True):
                return None
            reads_target = False
            def inspect(node):
                nonlocal reads_target
                if type(node).__name__ in ("NamedValueExpression",
                                            "HierarchicalValueExpression"):
                    try:
                        reads_target = reads_target or _array_storage_name(node.symbol) == base
                    except Exception:
                        reads_target = True
            _visit_selected_expression(element, inspect)
            if reads_target:
                return None
            value = convert_expr(sm, element)
            if (value is None or value.get("kind") == "Unsupported"
                    or width_of(value) != width or not _case_expression_ok(value)):
                return None
            if two_state:
                value = squash2_wrap(value, width)
            values.append(value)
        return {"kind": "Block", "span": node_span(sm, expr),
                "stmts": [{
                    "kind": "BlockingAssign",
                    "span": node_span(sm, expr),
                    "target": {"kind": "Ident", "span": node_span(sm, lhs),
                               "width": width, "name": f"{base}[{index}]"},
                    "value": value,
                } for index, value in enumerate(values)],
                "dynamic_array_pattern_lowered": True}
    except Exception:
        return None


def _dynamic_array_concat_assignment(sm, expr):
    """Lower a finite unpacked concatenation with fixed-array operands.

    The dynamic destination already has one flat cell per sampled element.
    A concatenation contributes scalar leaves in source order; a fixed
    unpacked scalar array contributes its cells in declaration order.  Keep
    this path blocking, integral, effect-free, exact-width, and alias-free so
    the cell expansion preserves the single RHS snapshot required by §10.10.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None or expr.isNonBlocking
                or type(expr.left).__name__ != "NamedValueExpression"):
            return None
        lhs = expr.left
        array_type = lhs.type.canonicalType
        if type(array_type).__name__ != "DynamicArrayType":
            return None
        rhs = expr.right
        while type(rhs).__name__ == "ConversionExpression":
            rhs = getattr(rhs, "operand", None)
            if rhs is None:
                return None
        if type(rhs).__name__ != "ConcatenationExpression":
            return None
        extent = _dynamic_array_constant_extent(lhs.symbol)
        if extent is None:
            return None
        element_type = array_type.elementType
        width, two_state, reason = type_width_2s(element_type)
        if width is None or reason is not None:
            return None
        destination = _array_storage_name(lhs.symbol)
        values = []

        def append_scalar(node):
            if not _case_source_expression_ok(node, packed_members=True):
                return False
            reads_destination = False

            def inspect(selected):
                nonlocal reads_destination
                if type(selected).__name__ in ("NamedValueExpression",
                                                "HierarchicalValueExpression"):
                    try:
                        reads_destination = (reads_destination or
                                             _array_storage_name(selected.symbol)
                                             == destination)
                    except Exception:
                        reads_destination = True

            _visit_selected_expression(node, inspect)
            if reads_destination:
                return False
            value = convert_expr(sm, node)
            if (value is None or value.get("kind") == "Unsupported"
                    or width_of(value) != width or not _case_expression_ok(value)):
                return False
            values.append(squash2_wrap(value, width) if two_state else value)
            return True

        def flatten(node):
            while type(node).__name__ == "ConversionExpression":
                node = getattr(node, "operand", None)
                if node is None:
                    return False
            if type(node).__name__ == "ConcatenationExpression":
                operands = list(getattr(node, "operands", []))
                return bool(operands) and all(flatten(item) for item in operands)
            shape = _fixed_array_assignment_shape(node)
            if shape is not None:
                source_name, source_width, _source_two, positions = shape
                source_type = getattr(getattr(node, "type", None),
                                       "canonicalType", None)
                if (type(source_type).__name__ != "FixedSizeUnpackedArrayType"
                        or source_width != width or source_name == destination
                        or not _case_source_expression_ok(node)):
                    return False
                for position in positions:
                    values.append({
                        "kind": "Ident", "span": node_span(sm, node),
                        "width": width,
                        "name": f"{source_name}[{position}]",
                    })
                return True
            return append_scalar(node)

        if not flatten(rhs) or len(values) != extent:
            return None
        span = node_span(sm, expr)
        return {
            "kind": "Block", "span": span,
            "stmts": [{
                "kind": "BlockingAssign", "span": span,
                "target": {"kind": "Ident", "span": node_span(sm, lhs),
                           "width": width, "name": f"{destination}[{index}]"},
                "value": value,
            } for index, value in enumerate(values)],
            "dynamic_array_concat_lowered": True,
        }
    except Exception:
        return None


def _dynamic_fixed_size_mismatch(sm, expression):
    """Recognize the IEEE 7.6 dynamic-to-fixed size mismatch.

    Assigning a sampled dynamic array to a fixed-size unpacked array with a
    different element count is a run-time error and performs no copy.  The
    self-check surface has no diagnostic channel or aggregate store, so the
    caller represents this exact blocking form by an immediate ``$finish``.
    Keep equal-size copies on the existing cell-by-cell lowering and reject
    dynamic/side-effecting, nonblocking, and timed forms here.
    """
    try:
        if (type(expression).__name__ != "AssignmentExpression"
                or expression.op is not None
                or expression.timingControl is not None
                or expression.isNonBlocking):
            return None
        lhs = expression.left
        rhs = expression.right
        lhs_shape = _fixed_array_shape(lhs)
        rhs_shape = _fixed_array_shape(rhs)
        if lhs_shape is None or rhs_shape is None:
            return None
        lhs_type = getattr(lhs.type, "canonicalType", lhs.type)
        rhs_source = rhs
        while type(rhs_source).__name__ == "ConversionExpression":
            rhs_source = getattr(rhs_source, "operand", None)
            if rhs_source is None:
                return None
        rhs_type = getattr(rhs_source.type, "canonicalType", rhs_source.type)
        if (type(lhs_type).__name__ != "FixedSizeUnpackedArrayType"
                or type(rhs_type).__name__ != "DynamicArrayType"):
            return None
        lhs_name, lhs_width, _lhs_two, lhs_left, lhs_right = lhs_shape
        rhs_name, rhs_width, _rhs_two, rhs_left, rhs_right = rhs_shape
        lhs_count = abs(lhs_left - lhs_right) + 1
        rhs_count = abs(rhs_left - rhs_right) + 1
        if (lhs_count == rhs_count or lhs_width != rhs_width
                or lhs_name == rhs_name):
            return None
        # A sampled dynamic array is a plain variable in the admitted shape;
        # other source expressions could carry evaluation effects that the
        # immediate-halt abstraction must not erase.
        if type(rhs_source).__name__ != "NamedValueExpression":
            return None
        if str(getattr(rhs_source.symbol, "kind", "")) != "SymbolKind.Variable":
            return None
        return {"kind": "SysCall", "span": node_span(sm, expression),
                "name": "$finish", "format": None, "args": [],
                "arg_signed": [], "dynamic_fixed_size_mismatch": True}
    except Exception:
        return None


def _fixed_array_indexed_slice_info(sm, expression):
    """Describe a runtime indexed slice over a one-dimensional fixed array.

    The legacy state has one vector per array cell, so an indexed slice is
    admitted only when its element count is a positive constant and every
    possible start can be enumerated.  The runtime start is kept as a pure
    converted expression; invalid starts fall through to the all-``x`` read
    or no-op write supplied by the caller.
    """
    try:
        if type(expression).__name__ != "RangeSelectExpression":
            return None
        selection = str(expression.selectionKind).split(".")[-1]
        if selection not in ("IndexedUp", "IndexedDown"):
            return None
        shape = _fixed_array_shape(expression.value)
        if shape is None:
            return None
        name, width, two_state, array_left, array_right = shape
        count = _constant_dimension_selector(expression.right)
        if count is None or count <= 0:
            return None
        lo, hi = min(array_left, array_right), max(array_left, array_right)
        if count > hi - lo + 1 or count > 1024:
            return None
        index = expression.left
        if _constant_dimension_selector(index) is not None:
            # Constant indexed slices are intentionally kept on the dynamic
            # path only when they are actually runtime expressions.  The
            # existing constant simple-slice lowering remains the narrow
            # aggregate path for declarations and reads.
            return None
        index_width, _index_two, index_reason = type_width_2s(index.type)
        if (index_width is None or index_reason is not None
                or not _case_source_expression_ok(index)):
            return None
        converted_index = convert_expr(sm, index)
        if (converted_index is None or not _case_expression_ok(converted_index)
                or width_of(converted_index) != index_width):
            return None
        direction = 1 if selection == "IndexedUp" else -1
        if direction > 0:
            starts = list(range(lo, hi - count + 2))
        else:
            starts = list(range(lo + count - 1, hi + 1))
        if not starts:
            return None
        return {
            "name": name,
            "width": width,
            "two_state": two_state,
            "count": count,
            "direction": direction,
            "starts": starts,
            "index": index,
            "index_width": index_width,
            "converted_index": converted_index,
            "span": node_span(sm, expression),
        }
    except Exception:
        return None


def _fixed_array_dynamic_index_reads_root(expression, root_name):
    """Whether a runtime index expression reads a flattened array root."""
    try:
        reads = False

        def inspect(node):
            nonlocal reads
            if type(node).__name__ in ("NamedValueExpression",
                                       "HierarchicalValueExpression"):
                try:
                    reads = reads or _array_storage_name(node.symbol) == root_name
                except Exception:
                    reads = True

        _visit_selected_expression(expression, inspect)
        return reads
    except Exception:
        return True


def _fixed_array_dynamic_indexed_cell_read(info, offset):
    """Build one cell of a runtime indexed slice as a finite conditional."""
    width = info["width"]
    result = {
        "kind": "Literal",
        "span": info["span"],
        "width": width,
        "bits": "x" * width,
    }
    mask = (1 << info["index_width"]) - 1
    for start in reversed(info["starts"]):
        position = start + info["direction"] * offset
        literal = {
            "kind": "Literal",
            "span": info["span"],
            "width": info["index_width"],
            "bits": format(start & mask, f"0{info['index_width']}b"),
        }
        result = {
            "kind": "Ternary",
            "span": info["span"],
            "width": width,
            "cond": {
                "kind": "Binary",
                "span": info["span"],
                "width": 1,
                "op": "===",
                "left": info["converted_index"],
                "right": literal,
            },
            "then": {
                "kind": "Ident",
                "span": info["span"],
                "width": width,
                "name": f"{info['name']}[{position}]",
            },
            "else": result,
        }
    return squash2_wrap(result, width) if info["two_state"] else result


def _fixed_array_dynamic_slice_assignment(sm, expr):
    """Lower ``A[i +: c] = B[j -: c]`` cell by cell.

    Both starts are pure runtime expressions and ``c`` is a positive constant.
    Source and destination roots must differ: a sequential cell expansion of
    an overlapping self-copy would expose an earlier write to a later source
    read.  Each branch reads the source slice through a complete conditional
    snapshot before issuing its destination writes; invalid destination starts
    execute no branch, matching an unpacked-slice no-op.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None
                or type(expr.left).__name__ != "RangeSelectExpression"
                or type(expr.right).__name__ != "RangeSelectExpression"):
            return None
        lhs = _fixed_array_indexed_slice_info(sm, expr.left)
        rhs = _fixed_array_indexed_slice_info(sm, expr.right)
        if lhs is None or rhs is None:
            return None
        if (lhs["name"] == rhs["name"] or lhs["count"] != rhs["count"]
                or lhs["width"] != rhs["width"]):
            return None
        # A source index that reads the destination root could change after
        # the first blocking cell update.  Refuse that alias-sensitive shape.
        if _fixed_array_dynamic_index_reads_root(rhs["index"], lhs["name"]):
            return None
        result = None
        for start in reversed(lhs["starts"]):
            stmts = []
            for offset in range(lhs["count"]):
                position = start + lhs["direction"] * offset
                value = _fixed_array_dynamic_indexed_cell_read(rhs, offset)
                if lhs["two_state"]:
                    value = squash2_wrap(value, lhs["width"])
                stmts.append({
                    "kind": ("NonblockingAssign" if expr.isNonBlocking
                              else "BlockingAssign"),
                    "span": node_span(sm, expr),
                    "target": {
                        "kind": "Ident",
                        "span": node_span(sm, expr.left),
                        "width": lhs["width"],
                        "name": f"{lhs['name']}[{position}]",
                    },
                    "value": value,
                })
            literal = {
                "kind": "Literal",
                "span": lhs["span"],
                "width": lhs["index_width"],
                "bits": format(start & ((1 << lhs["index_width"]) - 1),
                                f"0{lhs['index_width']}b"),
            }
            result = {
                "kind": "If",
                "span": node_span(sm, expr),
                "cond": {
                    "kind": "Binary",
                    "span": lhs["span"],
                    "width": 1,
                    "op": "===",
                    "left": lhs["converted_index"],
                    "right": literal,
                },
                "then": {"kind": "Block", "span": node_span(sm, expr),
                         "stmts": stmts},
                "else": result,
            }
        return result
    except Exception:
        return None


def _fixed_array_bitstream_cast_assignment(sm, expr):
    """Expand an integral bit-stream cast into fixed-array leaf writes.

    IEEE 1800 §6.24.3 maps the most-significant source bits to element zero
    and then walks the destination dimensions in declaration order.  The
    legacy state already stores each bounded array leaf as an independent
    vector, so a cast with equal total widths can be represented by constant
    source windows.  Dynamic/queue/aggregate leaves and mismatched widths stay
    loud rather than receiving a fabricated aggregate value.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None
                or type(expr.right).__name__ != "ConversionExpression"
                or str(expr.right.conversionKind).split(".")[-1] != "BitstreamCast"):
            return None
        lhs = expr.left
        if not _storage_expression(lhs):
            return None
        dims_shape = _fixed_array_dimensions(lhs.type)
        if dims_shape is None:
            return None
        dimensions, leaf_type = dims_shape
        if type(leaf_type).__name__ in ("FixedSizeUnpackedArrayType",
                                        "UnpackedStructType", "UnpackedUnionType",
                                        "DynamicArrayType", "QueueType",
                                        "AssociativeArrayType"):
            return None
        leaf_width, leaf_two, leaf_reason = type_width_2s(leaf_type)
        source_width, _source_two, source_reason = type_width_2s(expr.right.operand.type)
        if (leaf_width is None or leaf_reason is not None
                or source_width is None or source_reason is not None):
            return None
        count = 1
        positions = [()]
        for left, right in dimensions:
            step = 1 if right >= left else -1
            axis = list(range(int(left), int(right) + step, step))
            count *= len(axis)
            positions = [prefix + (position,)
                         for prefix in positions for position in axis]
        if count <= 0 or count > 1024 or count * leaf_width != source_width:
            return None
        if not _case_source_expression_ok(expr.right.operand):
            return None
        source = convert_expr(sm, expr.right.operand)
        if source is None or not _case_expression_ok(source):
            return None
        root = _array_storage_name(lhs.symbol)
        stmts = []
        for index, suffix in enumerate(positions):
            offset = source_width - (index + 1) * leaf_width
            value = {
                "kind": "SelectRead",
                "span": node_span(sm, expr.right),
                "width": leaf_width,
                "value": source,
                "index": {
                    "kind": "Literal",
                    "span": node_span(sm, expr.right),
                    "width": 32,
                    "bits": format(offset & ((1 << 32) - 1), "032b"),
                },
                "index_signed": False,
                "descending": False,
            }
            if leaf_two:
                value = squash2_wrap(value, leaf_width)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {
                    "kind": "Ident",
                    "span": node_span(sm, expr.left),
                    "width": leaf_width,
                    "name": root + "".join(f"[{position}]" for position in suffix),
                },
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts,
                "fixed_array_bitstream_cast_lowered": True}
    except Exception:
        return None


def _fixed_array_struct_pattern_assignment(sm, expr):
    """Expand a complete positional pattern of integral struct elements."""
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None or not _storage_expression(expr.left)):
            return None
        array_type = expr.left.type.canonicalType
        if type(array_type).__name__ != "FixedSizeUnpackedArrayType":
            return None
        element_type = array_type.elementType.canonicalType
        if type(element_type).__name__ != "UnpackedStructType":
            return None
        if getattr(element_type, "isTagged", False):
            return None
        if type(expr.right).__name__ not in (
                "SimpleAssignmentPatternExpression",
                "StructuredAssignmentPatternExpression",
                "ReplicatedAssignmentPatternExpression"):
            return None
        left, right = int(array_type.range.left), int(array_type.range.right)
        positions = list(range(left, right + (1 if right >= left else -1),
                               1 if right >= left else -1))
        elements = _pattern_source_elements(expr.right)
        if not elements:
            return None
        if type(expr.right).__name__ == "ReplicatedAssignmentPatternExpression":
            repetition = getattr(getattr(expr.right, "count", None), "constant", None)
            try:
                if hasattr(repetition, "value"):
                    repetition = repetition.value
                repetition = int(repetition)
            except (TypeError, ValueError, OverflowError):
                return None
            if repetition <= 0 or repetition * len(elements) != len(positions):
                return None
            elements = elements * repetition
        if len(elements) != len(positions):
            return None
        root = _array_storage_name(expr.left.symbol)
        cells = []
        for position, element in zip(positions, elements):
            if type(element).__name__ not in (
                    "SimpleAssignmentPatternExpression",
                    "StructuredAssignmentPatternExpression"):
                return None
            reads_target = False
            def inspect(node):
                nonlocal reads_target
                if type(node).__name__ in ("NamedValueExpression",
                                           "HierarchicalValueExpression"):
                    try:
                        reads_target = reads_target or _array_storage_name(node.symbol) == root
                    except Exception:
                        reads_target = True
            _visit_selected_expression(element, inspect)
            if reads_target:
                return None
            fields = _unpacked_struct_initializer_cells(
                sm, f"{root}[{position}]", element_type, element)
            if fields is None:
                return None
            cells.extend(fields)
        stmts = []
        for name, width, value, field_type in cells:
            if value is None:
                return None
            if not field_type.isFourState:
                value = squash2_wrap(value, width)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                           "width": width, "name": name},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts,
                "fixed_array_struct_pattern_lowered": True}
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
        lhs_name = None
        if _storage_expression(lhs):
            if str(lhs.symbol.kind) != "SymbolKind.Variable":
                return None
            lhs_type = lhs.type.canonicalType
            lhs_name = _array_storage_name(lhs.symbol)
        else:
            # A fixed array field of an unpacked struct is flattened into the
            # same independent cells as a top-level array.  Resolve its
            # member path here so a positional pattern can target those cells
            # without introducing aggregate storage.
            path = _unpacked_struct_path(lhs)
            if path is None:
                return None
            lhs_name, selected_type = path
            lhs_type = selected_type
            root = lhs
            while type(root).__name__ == "MemberAccessExpression":
                root = root.value
            if (not _storage_expression(root)
                    or str(root.symbol.kind) != "SymbolKind.Variable"):
                return None
        lhs_type = lhs_type.canonicalType
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
        target_name = lhs_name
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
                if type(node).__name__ == "ElementSelectExpression":
                    selected = _fixed_array_selection_prefix(node)
                    if (selected is not None
                            and selected[0].startswith(target_name + "[")):
                        reads_target = True
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


def _fixed_array_nested_pattern_assignment(sm, expr):
    """Lower complete assignment patterns over nested fixed arrays.

    Declaration lowering already flattens finite dimensions with
    `_fixed_array_pattern_elements`; use the same expansion for procedural
    writes so each leaf is an ordinary vector-cell assignment. Dynamic,
    partial, aggregate-element, and aliasing patterns remain unsupported.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None or not _storage_expression(expr.left)):
            return None
        array_type = expr.left.type.canonicalType
        if type(array_type).__name__ != "FixedSizeUnpackedArrayType":
            return None
        shape = _fixed_array_dimensions(array_type)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        if len(dimensions) <= 1:
            return None
        if type(leaf_type).__name__ in ("FixedSizeUnpackedArrayType", "UnpackedStructType",
                                        "UnpackedUnionType", "DynamicArrayType",
                                        "QueueType", "AssociativeArrayType"):
            return None
        width, two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None:
            return None
        pattern_kind = type(expr.right).__name__
        if pattern_kind not in ("SimpleAssignmentPatternExpression",
                                "StructuredAssignmentPatternExpression",
                                "ReplicatedAssignmentPatternExpression"):
            return None
        elements = _fixed_array_pattern_elements(expr.right, dimensions)
        if elements is None:
            return None
        positions = [()]
        for left, right in dimensions:
            step = 1 if right >= left else -1
            positions = [prefix + (position,)
                         for prefix in positions
                         for position in range(left, right + step, step)]
        if len(elements) != len(positions):
            return None
        base = _array_storage_name(expr.left.symbol)
        values = []
        for element in elements:
            if not _case_source_expression_ok(element, packed_members=True):
                return None
            reads_target = False
            def inspect(node):
                nonlocal reads_target
                if type(node).__name__ in ("NamedValueExpression", "HierarchicalValueExpression"):
                    try:
                        reads_target = reads_target or _array_storage_name(node.symbol) == base
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
        for indexes, value in zip(positions, values):
            name = base + "".join(f"[{position}]" for position in indexes)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                           "width": width, "name": name},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts,
                "fixed_array_nested_pattern_lowered": True}
    except Exception:
        return None


def _unpacked_struct_copy_assignment(sm, expr):
    """Lower a whole copy of a flattened integral unpacked struct.

    The legacy state stores each scalar/packed field as its own vector cell,
    so a copy can be expanded field by field while sampling the source before
    any destination update. Aggregate fields and self-copies stay loud.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None):
            return None
        lhs_path = _unpacked_struct_path(expr.left)
        rhs_path = _unpacked_struct_path(expr.right)
        if lhs_path is None or rhs_path is None:
            return None
        lhs_name, lhs_type = lhs_path
        rhs_name, rhs_type = rhs_path
        if (type(lhs_type).__name__ != "UnpackedStructType"
                or type(rhs_type).__name__ != "UnpackedStructType"
                or lhs_name == rhs_name):
            return None
        lhs_cells = _unpacked_struct_field_cells(lhs_name, lhs_type,
                                                 node_span(sm, expr))
        rhs_cells = _unpacked_struct_field_cells(rhs_name, rhs_type,
                                                 node_span(sm, expr))
        if (lhs_cells is None or rhs_cells is None or
                len(lhs_cells) != len(rhs_cells)):
            return None
        if any(lw != rw for (_, lw, _, _), (_, rw, _, _) in
               zip(lhs_cells, rhs_cells)):
            return None
        stmts = []
        for (lname, lwidth, _linit, ltype), (rname, rwidth, _rinit, _rtype) in zip(
                lhs_cells, rhs_cells):
            value = {"kind": "Ident", "span": node_span(sm, expr.right),
                     "width": rwidth, "name": rname}
            if not ltype.isFourState:
                value = squash2_wrap(value, lwidth)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                           "width": lwidth, "name": lname},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts,
                "unpacked_struct_copy_lowered": True}
    except Exception:
        return None


def _fixed_array_oob_struct_select(expression):
    """Recognize a fully constant out-of-bounds fixed-array struct read."""
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
        out_of_range = any(
            position < min(left, right) or position > max(left, right)
            for position, (left, right) in zip(reversed(selectors), dimensions))
        if not out_of_range:
            return None
        aggregate = leaf_type.canonicalType
        if type(aggregate).__name__ != "UnpackedStructType":
            return None
        return aggregate
    except Exception:
        return None


def _unpacked_struct_oob_defaults(sm, base_name, aggregate, span, seen=None):
    """Flatten IEEE §7.4.5 defaults for an out-of-bounds struct value."""
    if seen is None:
        seen = set()
    try:
        marker = id(aggregate)
        if marker in seen or type(aggregate).__name__ != "UnpackedStructType":
            return None
        seen = seen | {marker}
        fields = list(aggregate)
        if not fields:
            return None
        cells = []
        for field in fields:
            leaf = field.type.canonicalType
            name = f"{base_name}.{field.name}"
            if type(leaf).__name__ == "UnpackedStructType":
                nested = _unpacked_struct_oob_defaults(sm, name, leaf, span, seen)
                if nested is None:
                    return None
                cells.extend(nested)
                continue
            width, _two_state, reason = type_width_2s(field.type)
            if (width is None or reason is not None or type(leaf).__name__ in
                    ("FixedSizeUnpackedArrayType", "DynamicArrayType",
                     "QueueType", "AssociativeArrayType", "UnpackedUnionType")):
                return None
            initializer = getattr(field, "initializer", None)
            if initializer is not None:
                value = convert_expr(sm, initializer)
                if (value is None or width_of(value) != width
                        or not _case_expression_ok(value)):
                    return None
            else:
                value = {"kind": "Literal", "span": span, "width": width,
                         "bits": ("0" if not field.type.isFourState else "x") * width}
            cells.append((name, width, value, field.type))
        return cells
    except Exception:
        return None


def _unpacked_struct_oob_assignment(sm, expr):
    """Assign an out-of-bounds fixed-array struct read field by field."""
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None):
            return None
        lhs_path = _unpacked_struct_path(expr.left)
        source_type = _fixed_array_oob_struct_select(expr.right)
        if lhs_path is None or source_type is None:
            return None
        lhs_name, lhs_type = lhs_path
        if type(lhs_type).__name__ != "UnpackedStructType":
            return None
        lhs_cells = _unpacked_struct_field_cells(lhs_name, lhs_type,
                                                 node_span(sm, expr))
        values = _unpacked_struct_oob_defaults(
            sm, "$oob", source_type, node_span(sm, expr))
        if lhs_cells is None or values is None or len(lhs_cells) != len(values):
            return None
        if any(lwidth != vwidth for (_lname, lwidth, _init, _ltype),
               (_vname, vwidth, _value, _vtype) in zip(lhs_cells, values)):
            return None
        stmts = []
        for (name, width, _init, ltype), (_vname, _vwidth, value, _vtype) in zip(
                lhs_cells, values):
            if not ltype.isFourState:
                value = squash2_wrap(value, width)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                           "width": width, "name": name},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts,
                "unpacked_struct_oob_lowered": True}
    except Exception:
        return None


def _unpacked_struct_pattern_assignment(sm, expr):
    """Lower a complete positional assignment pattern for an integral struct."""
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None):
            return None
        path = _unpacked_struct_path(expr.left)
        if path is None:
            return None
        name, aggregate = path
        if type(aggregate).__name__ != "UnpackedStructType":
            return None
        pattern = expr.right
        if type(pattern).__name__ not in (
                "SimpleAssignmentPatternExpression",
                "StructuredAssignmentPatternExpression"):
            return None
        # Nested structs and finite array fields are normalized recursively by
        # the same cell flattener used for declaration initializers. Reuse
        # those converted leaf values so keyed/default patterns and two-state
        # fields keep exactly the declaration-path behavior.
        if any(type(field.type.canonicalType).__name__ in (
                "UnpackedStructType", "FixedSizeUnpackedArrayType")
               for field in aggregate):
            target_root = name.split(".", 1)[0].split("[", 1)[0]
            reads_target = False

            def inspect(node):
                nonlocal reads_target
                if type(node).__name__ in (
                        "NamedValueExpression", "HierarchicalValueExpression"):
                    try:
                        reads_target = (reads_target or
                                        _storage_name(node.symbol) == target_root)
                    except Exception:
                        reads_target = True

            _visit_selected_expression(pattern, inspect)
            if reads_target:
                return None
            nested_cells = _unpacked_struct_initializer_cells(
                sm, name, aggregate, pattern)
            if nested_cells is None:
                return None
            stmts = [{
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                           "width": width, "name": cell_name},
                "value": value,
            } for cell_name, width, value, _field_type in nested_cells]
            return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts,
                    "unpacked_struct_pattern_lowered": True}
        fields = list(aggregate)
        elements = list(pattern.elements)
        if len(fields) != len(elements) or not fields:
            return None
        cells = _unpacked_struct_field_cells(name, aggregate, node_span(sm, expr))
        if cells is None or len(cells) != len(fields):
            return None
        stmts = []
        for field, element, (cell_name, width, _init, field_type) in zip(
                fields, elements, cells):
            if not _case_source_expression_ok(element, packed_members=True):
                return None
            value = convert_expr(sm, element)
            if (value is None or value.get("kind") == "Unsupported"
                    or width_of(value) != width or not _case_expression_ok(value)):
                return None
            if not field_type.isFourState:
                value = squash2_wrap(value, width)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                           "width": width, "name": cell_name},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts,
                "unpacked_struct_pattern_lowered": True}
    except Exception:
        return None


def _unpacked_struct_conditional_assignment(sm, expr):
    """Lower a pure conditional whole-struct assignment field by field.

    An unpacked struct has no aggregate slot in the legacy state.  A
    conditional expression therefore becomes one ternary per flattened leaf;
    this preserves X merging in the existing vector evaluator and samples the
    condition once for the whole assignment.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None
                or type(expr.right).__name__ != "ConditionalExpression"):
            return None
        lhs_path = _unpacked_struct_path(expr.left)
        if lhs_path is None:
            return None
        lhs_name, lhs_type = lhs_path
        if type(lhs_type).__name__ != "UnpackedStructType":
            return None
        conditional = expr.right
        if (len(conditional.conditions) != 1
                or conditional.conditions[0].pattern is not None):
            return None
        then_path = _unpacked_struct_path(conditional.left)
        else_path = _unpacked_struct_path(conditional.right)
        if then_path is None or else_path is None:
            return None
        then_name, then_type = then_path
        else_name, else_type = else_path
        if (type(then_type).__name__ != "UnpackedStructType"
                or type(else_type).__name__ != "UnpackedStructType"
                or lhs_name in (then_name, else_name)):
            return None
        lhs_cells = _unpacked_struct_field_cells(lhs_name, lhs_type,
                                                 node_span(sm, expr))
        then_cells = _unpacked_struct_field_cells(then_name, then_type,
                                                  node_span(sm, expr))
        else_cells = _unpacked_struct_field_cells(else_name, else_type,
                                                  node_span(sm, expr))
        if (lhs_cells is None or then_cells is None or else_cells is None
                or len(lhs_cells) != len(then_cells)
                or len(lhs_cells) != len(else_cells)):
            return None
        source_cond = conditional.conditions[0].expr
        if not _case_source_expression_ok(source_cond):
            return None
        condition = convert_expr(sm, source_cond)
        if condition is None or not _case_expression_ok(condition):
            return None
        stmts = []
        for (lname, lwidth, _linit, ltype), (tname, twidth, _tinit, _ttype), \
                (ename, ewidth, _einit, _etype) in zip(lhs_cells, then_cells, else_cells):
            if lwidth != twidth or lwidth != ewidth:
                return None
            value = {
                "kind": "Ternary", "span": node_span(sm, expr.right),
                "width": lwidth, "cond": condition,
                "then": {"kind": "Ident", "span": node_span(sm, conditional.left),
                          "width": twidth, "name": tname},
                "else": {"kind": "Ident", "span": node_span(sm, conditional.right),
                         "width": ewidth, "name": ename},
            }
            if not ltype.isFourState:
                value = squash2_wrap(value, lwidth)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                           "width": lwidth, "name": lname},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts,
                "unpacked_struct_conditional_lowered": True}
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
            if type(pattern_type).__name__ not in (
                    "FixedSizeUnpackedArrayType", "DynamicArrayType"):
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
        rhs_source = rhs
        while type(rhs_source).__name__ == "ConversionExpression":
            rhs_source = getattr(rhs_source, "operand", None)
            if rhs_source is None:
                return None
        rhs_is_net = (str(getattr(getattr(rhs_source, "symbol", None), "kind", ""))
                      == "SymbolKind.Net")
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
        result = {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts}
        if rhs_is_net:
            result["fixed_array_net_copy_lowered"] = True
        return result
    except Exception:
        return None


def _fixed_array_nested_copy_assignment(sm, expr):
    """Lower a whole bounded multidimensional fixed-array copy.

    The legacy state expands every bounded integral leaf to an ordinary vector
    cell, so an assignment between two distinct arrays can be copied in
    declaration order without an aggregate store.  Require the same finite
    dimension counts and leaf width; differing declared bounds are still
    assignment-compatible when their ordinal shapes agree.  Dynamic,
    aggregate, aliased, and effectful forms stay on the target boundary.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None):
            return None
        lhs, rhs = expr.left, expr.right
        if not (_storage_expression(lhs) and _storage_expression(rhs)):
            return None
        lhs_shape = _fixed_array_dimensions(lhs.type)
        rhs_shape = _fixed_array_dimensions(rhs.type)
        if lhs_shape is None or rhs_shape is None:
            return None
        lhs_dims, lhs_leaf = lhs_shape
        rhs_dims, rhs_leaf = rhs_shape
        if len(lhs_dims) <= 1 or len(lhs_dims) != len(rhs_dims):
            return None
        lhs_width, _lhs_two, lhs_reason = type_width_2s(lhs_leaf)
        rhs_width, _rhs_two, rhs_reason = type_width_2s(rhs_leaf)
        if (lhs_width is None or rhs_width is None or lhs_reason is not None
                or rhs_reason is not None or lhs_width != rhs_width):
            return None
        lhs_counts = [abs(left - right) + 1 for left, right in lhs_dims]
        rhs_counts = [abs(left - right) + 1 for left, right in rhs_dims]
        if lhs_counts != rhs_counts:
            return None
        lhs_root = _array_storage_name(lhs.symbol)
        rhs_root = _array_storage_name(rhs.symbol)
        if not lhs_root or not rhs_root or lhs_root == rhs_root:
            return None
        if not _case_source_expression_ok(rhs):
            return None

        def cells(root, dimensions):
            positions = [()]
            for left, right in dimensions:
                step = 1 if right >= left else -1
                positions = [prefix + (position,)
                             for prefix in positions
                             for position in range(left, right + step, step)]
            return [root + "".join(f"[{position}]" for position in indexes)
                    for indexes in positions]

        lhs_cells = cells(lhs_root, lhs_dims)
        rhs_cells = cells(rhs_root, rhs_dims)
        if len(lhs_cells) != len(rhs_cells):
            return None
        stmts = []
        for lhs_name, rhs_name in zip(lhs_cells, rhs_cells):
            value = {"kind": "Ident", "span": node_span(sm, rhs),
                     "width": rhs_width, "name": rhs_name}
            if not lhs_leaf.isFourState:
                value = squash2_wrap(value, lhs_width)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, lhs),
                           "width": lhs_width, "name": lhs_name},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr),
                "stmts": stmts,
                "fixed_array_nested_copy_lowered": True}
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


def _fixed_array_struct_copy_assignment(sm, expr):
    """Copy a finite fixed array whose leaves are integral unpacked structs."""
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None):
            return None
        lhs, rhs = expr.left, expr.right
        if not (_storage_expression(lhs) and _storage_expression(rhs)):
            return None
        lhs_shape = _fixed_array_dimensions(lhs.type)
        rhs_shape = _fixed_array_dimensions(rhs.type)
        if lhs_shape is None or rhs_shape is None:
            return None
        lhs_dims, lhs_leaf = lhs_shape
        rhs_dims, rhs_leaf = rhs_shape
        if (lhs_dims != rhs_dims
                or type(lhs_leaf).__name__ != "UnpackedStructType"
                or type(rhs_leaf).__name__ != "UnpackedStructType"):
            return None
        lhs_root = _array_storage_name(lhs.symbol)
        rhs_root = _array_storage_name(rhs.symbol)
        if lhs_root == rhs_root or not _case_source_expression_ok(rhs):
            return None
        positions = [()]
        for left, right in lhs_dims:
            step = 1 if right >= left else -1
            positions = [prefix + (position,)
                         for prefix in positions
                         for position in range(left, right + step, step)]
        stmts = []
        for indexes in positions:
            lhs_base = lhs_root + "".join(f"[{position}]" for position in indexes)
            rhs_base = rhs_root + "".join(f"[{position}]" for position in indexes)
            lhs_cells = _unpacked_struct_field_cells(lhs_base, lhs_leaf,
                                                     node_span(sm, expr))
            rhs_cells = _unpacked_struct_field_cells(rhs_base, rhs_leaf,
                                                     node_span(sm, expr))
            if (lhs_cells is None or rhs_cells is None
                    or len(lhs_cells) != len(rhs_cells)):
                return None
            for (lname, lwidth, _linit, ltype), (rname, rwidth, _rinit, _rtype) in zip(
                    lhs_cells, rhs_cells):
                if lwidth != rwidth:
                    return None
                value = {"kind": "Ident", "span": node_span(sm, rhs),
                         "width": rwidth, "name": rname}
                if not ltype.isFourState:
                    value = squash2_wrap(value, lwidth)
                stmts.append({
                    "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                    "span": node_span(sm, expr),
                    "target": {"kind": "Ident", "span": node_span(sm, lhs),
                               "width": lwidth, "name": lname},
                    "value": value,
                })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts,
                "fixed_array_struct_copy_lowered": True}
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
    if cname == "TimeLiteral":
        return _convert_time_literal(sm, e)
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
    # The self-check executor has no elapsed-time state, so a real-valued
    # `$realtime` query is exactly zero at the only point this surface runs.
    # Keep the real value itself opaque, but admit the standard conversion
    # boundary when the surrounding context requests an integral result.
    # This is deliberately before the ordinary width machinery: a real source
    # has no integral ``bitWidth`` for that machinery to inspect.
    if (_SYM is None and _realtime_call(getattr(e, "operand", None))
            and getattr(e.type, "isIntegral", False)):
        width, _, reason = type_width_2s(e.type)
        if width is not None and reason is None and width > 0:
            return {
                "kind": "Literal",
                "span": node_span(sm, e),
                "width": width,
                "bits": "0" * width,
                "time_zero": True,
                "realtime_conversion": True,
            }
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
    if _SYM is None and skind in ("Variable", "Net"):
        union_shape = _unpacked_union_shape(e.type)
        if union_shape is not None:
            width, _two_state = union_shape
            return signed_metadata({
                "kind": "Ident",
                "span": node_span(sm, e),
                "width": width,
                "name": _storage_name(sym),
            }, e.type)
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
    if (_SYM is None and sym not in ("==", "!=", "===", "!==")
            and (_unpacked_union_shape(getattr(e.left, "type", None)) is not None
                 or _unpacked_union_shape(getattr(e.right, "type", None)) is not None)):
        return unsupported(sm, e, "BinaryExpression:unpacked-union")
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
    union_shape = (_unpacked_union_shape(e.type) if _SYM is None else None)
    if union_shape is not None:
        left_shape = _unpacked_union_shape(e.left.type)
        right_shape = _unpacked_union_shape(e.right.type)
        if left_shape != union_shape or right_shape != union_shape:
            return unsupported(sm, e, "ConditionalExpression:union-shape")
        width = union_shape[0]
    else:
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
        # At the leaf a pattern element must be one scalar/packed value.  An
        # enum type-key pattern is still a scalar value; let the ordinary
        # packed-pattern converter preserve its declared enum literal.  Other
        # composite patterns are consumed by the enclosing unpacked dimension.
        if type(pattern).__name__ in (
                "SimpleAssignmentPatternExpression",
                "StructuredAssignmentPatternExpression",
                "ReplicatedAssignmentPatternExpression"):
            scalar_pattern = False
            if type(pattern).__name__ == "StructuredAssignmentPatternExpression":
                canonical = type(pattern.type.canonicalType).__name__
                scalar_pattern = canonical == "EnumType"
                if (canonical == "PredefinedIntegerType"
                        and getattr(pattern, "typeSetters", [])
                        and not getattr(pattern, "indexSetters", [])
                        and not getattr(pattern, "memberSetters", [])):
                    scalar_pattern = all(
                        type(getattr(setter.type, "canonicalType", None)).__name__
                        == "EnumType"
                        for setter in pattern.typeSetters)
            if not scalar_pattern:
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
            "PredefinedIntegerType", "EnumType", "PackedArrayType",
            "PackedStructType"):
        return unsupported(sm, expression, "AssignmentPattern:integral-shape")
    if kind == "PackedStructType":
        expected = [member.type.bitWidth for member in shape
                    if str(member.kind) == "SymbolKind.Field"]
    elif (kind == "EnumType"
          and type(expression).__name__ == "StructuredAssignmentPatternExpression"):
        # A type-keyed enum pattern is a scalar value, even though pyslang
        # exposes its default inventory as one bit per element.  Preserve the
        # enum key's declared value and require the remaining default arm to
        # be a pure literal.  This is the narrow form used when a packed
        # struct assignment pattern supplies ``state_t: BUSY``; arbitrary
        # enum patterns and effectful defaults remain outside the flat tier.
        setters = list(getattr(expression, "typeSetters", []))
        if (len(setters) != 1 or getattr(expression, "indexSetters", [])
                or getattr(expression, "memberSetters", [])):
            return unsupported(sm, expression, "AssignmentPattern:enum-key")
        setter = setters[0]
        try:
            if setter.type.canonicalType is not shape:
                return unsupported(sm, expression, "AssignmentPattern:enum-key")
            enum_expr = setter.expr
            symbol = enum_expr.symbol
            if (type(enum_expr).__name__ != "NamedValueExpression"
                    or str(symbol.kind) != "SymbolKind.EnumValue"):
                return unsupported(sm, expression, "AssignmentPattern:enum-key")
            default = getattr(expression, "defaultSetter", None)
            if (default is None or getattr(default, "bad", False)
                    or type(default).__name__ not in
                    ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral")
                    or not _case_source_expression_ok(default)):
                return unsupported(sm, expression, "AssignmentPattern:enum-default")
            value = symbol.value
            if hasattr(value, "value"):
                value = value.value
            if hasattr(value, "bitWidth"):
                bits = svint_bits(value)
            else:
                bits = format(int(value) & ((1 << width) - 1), f"0{width}b")
            return {
                "kind": "Literal", "span": node_span(sm, expression),
                "width": width, "bits": bits,
                "assignment_pattern_enum_key": True,
            }
        except Exception:
            return unsupported(sm, expression, "AssignmentPattern:enum-key")
    elif (kind == "PredefinedIntegerType"
          and type(expression).__name__ == "StructuredAssignmentPatternExpression"
          and all(type(getattr(setter.type, "canonicalType", None)).__name__
                  == "EnumType"
                  for setter in getattr(expression, "typeSetters", []))
          and not getattr(expression, "indexSetters", [])
          and not getattr(expression, "memberSetters", [])):
        # Within a packed-struct field, a literal default denotes the whole
        # scalar field.  Slang exposes the field's bit inventory, but the
        # assignment-pattern rule applies the default to that field value.
        default = getattr(expression, "defaultSetter", None)
        if (default is None or getattr(default, "bad", False)
                or type(default).__name__ not in
                ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral")
                or not _case_source_expression_ok(default)):
            return unsupported(sm, expression, "AssignmentPattern:scalar-default")
        try:
            value = default.value
            if hasattr(value, "value"):
                value = value.value
            return {
                "kind": "Literal", "span": node_span(sm, expression),
                "width": width,
                "bits": format(int(value) & ((1 << width) - 1), f"0{width}b"),
                "assignment_pattern_scalar_default": True,
            }
        except Exception:
            return unsupported(sm, expression, "AssignmentPattern:scalar-default")
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
        # A packed element wider than one bit needs its slice offset scaled by
        # the element width even when the outer range is the canonical
        # `[N-1:0]` spelling.  Returning false routes that shape through the
        # constant-label normalizer below.
        element = ct.elementType.canonicalType
        return (type(element).__name__ == "ScalarType"
                and int(ct.range.left) == ct.bitWidth - 1
                and int(ct.range.right) == 0)
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
        element_width = int(ct.elementType.canonicalType.bitWidth)
        offset = ((position - right) if left > right else (right - position)) * element_width
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
    """Normalize a dynamic integral packed label to an LVec offset.

    Wide packed elements scale the outer label by their element width;
    one-bit elements retain the signed, 32-bit widened arithmetic used by
    foreach iterators. Unknown/out-of-range offsets use selectedRead.
    Negative-range unsigned-index corner cases retain the existing boundary.
    """
    constant = _packed_constant_index(sm, source_type, index)
    if constant is not None or _constant_dimension_selector(index) is not None:
        return constant
    width, _, reason = type_width_2s(index.type)
    if (reason is not None or not _case_source_expression_ok(index)):
        return None
    value = _convert_expr(sm, index)
    if not _case_expression_ok(value):
        return None
    ct = source_type.canonicalType
    element_width = int(ct.elementType.canonicalType.bitWidth)
    if element_width == 1:
        if width != 32 or not index.type.isSigned:
            return None
        wide = width + 2
        value = {"kind": "SignedResize",
                 "span": node_span(sm, index), "width": wide,
                 "operand": value}
        right = {"kind": "Literal", "span": node_span(sm, index),
                 "width": wide,
                 "bits": format(int(ct.range.right) & ((1 << wide) - 1),
                                  f"0{wide}b")}
        left, right = (value, right) if ct.range.left > ct.range.right else (right, value)
        return {"kind": "Binary", "span": node_span(sm, index),
                "width": wide, "op": "-", "left": left, "right": right}, True
    if element_width != 1:
        if type(ct).__name__ != "PackedArrayType" or element_width <= 0:
            return None
        span = node_span(sm, index)

        def literal(number):
            mask = (1 << width) - 1
            return {"kind": "Literal", "span": span, "width": width,
                    "bits": format(number & mask, f"0{width}b")}

        def binary(op, left, right):
            return {"kind": "Binary", "span": span, "width": width,
                    "op": op, "left": left, "right": right}

        left, right = int(ct.range.left), int(ct.range.right)
        if left > right:
            offset = binary("-", value, literal(right)) if right else value
        else:
            offset = binary("-", literal(right), value)
        offset = binary("*", offset, literal(element_width))
        return offset, bool(index.type.isSigned)
    return None


def _packed_dynamic_indexed_index(sm, source_type, index, width, selection):
    """Normalize a dynamic indexed part-select on a packed range.

    ``_packed_element_index`` produces the flat offset of the runtime outer
    label. A one-bit range uses one flat bit per label; a nested packed range
    uses one flat chunk per label, so the selected width must be a whole number
    of element chunks. For an ascending declaration, ``+:`` starts at the
    high-label end of the selected window, while ``-:`` starts at its low-label
    end; both are represented as an increasing flat window. A descending
    declaration keeps the evaluator's ordinary indexed-select direction
    convention.
    """
    try:
        ct = source_type.canonicalType
        if (type(ct).__name__ != "PackedArrayType"
                or width <= 0
                or selection not in ("IndexedUp", "IndexedDown")):
            return None
        element_width = int(ct.elementType.canonicalType.bitWidth)
        if element_width <= 0 or width % element_width:
            return None
        count = width // element_width
        normalized = _packed_element_index(sm, source_type, index)
        if normalized is None:
            return None
        converted, index_signed = normalized
        descending_range = int(ct.range.left) > int(ct.range.right)
        descending_select = selection == "IndexedDown"
        # ``selectedRead`` takes the low flat offset for an increasing window
        # and the high flat offset for a descending one. The amount is the
        # number of complete packed chunks between the base label and that
        # endpoint, rather than the raw selected bit width.
        amount = ((element_width - 1) if (descending_range and descending_select)
                  else (count - 1) * element_width)
        if ((not descending_range and not descending_select)
                or (descending_range and descending_select)) and amount:
            span = node_span(sm, index)
            literal = {
                "kind": "Literal", "span": span,
                "width": converted["width"],
                "bits": format(amount & ((1 << converted["width"]) - 1),
                                 f"0{converted['width']}b"),
            }
            converted = {
                "kind": "Binary", "span": span,
                "width": converted["width"],
                "op": "+" if descending_range and descending_select else "-",
                "left": converted, "right": literal,
            }
        # Ascending ranges are already normalized to increasing flat offsets;
        # descending ranges retain the evaluator's IndexedDown convention.
        return converted, index_signed, (descending_range and descending_select)
    except Exception:
        return None


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
            # fail the fixed-cell admission above. A packed array is also a
            # single vector, so compose its constant element offset with the
            # selected field offset instead of manufacturing aggregate state.
            packed_source = getattr(value, "value", None)
            packed_type = getattr(getattr(packed_source, "type", None),
                                  "canonicalType", None)
            if (_storage_expression(packed_source)
                    and type(packed_type).__name__ == "PackedArrayType"
                    and type(packed_type.elementType.canonicalType).__name__
                    in ("PackedStructType", "PackedUnionType")
                    and not getattr(packed_type.elementType.canonicalType,
                                    "isTagged", False)):
                normalized = _packed_constant_index(
                    sm, packed_source.type, value.selector)
                if normalized is None:
                    return None
                literal, _ = normalized
                bits = literal.get("bits")
                if not isinstance(bits, str) or any(bit not in "01" for bit in bits):
                    return None
                base = packed_source
                aggregate = packed_type.elementType.canonicalType
                parent_offset = int(bits, 2)
            else:
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
    """Flatten a constant selection chain rooted at a packed member.

    Legacy selected reads/targets store one vector plus an LSB offset. Every
    constant element or part selection in a chain contributes a fixed local
    offset, so compose those offsets through the existing packed-member
    window. Dynamic, tagged and nonintegral forms remain outside this helper.
    """
    def member_window(node):
        try:
            kind = type(node).__name__
            if kind == "MemberAccessExpression":
                member = _packed_struct_member(sm, node)
                if member is None:
                    return None
                base, width, offset, two_state = member
                return base, width, offset, two_state, False
            if kind not in ("ElementSelectExpression", "RangeSelectExpression"):
                return None
            parent = member_window(node.value)
            if parent is None:
                return None
            base, _parent_width, parent_offset, _parent_two_state, _parent_descending = parent
            normalized = None
            if kind == "ElementSelectExpression":
                normalized = _packed_constant_index(
                    sm, node.value.type, node.selector)
            else:
                selection = str(node.selectionKind).split(".")[-1]
                if selection == "Simple":
                    normalized = _packed_constant_simple_index(
                        sm, node.value.type, node.left, node.right,
                        node.type.bitWidth)
                elif selection in ("IndexedUp", "IndexedDown"):
                    normalized = _packed_constant_indexed_index(
                        sm, node.value.type, node.left,
                        node.type.bitWidth, selection == "IndexedDown")
                else:
                    return None
            if normalized is None:
                return None
            local_index, _index_signed = normalized
            bits = local_index.get("bits")
            if not isinstance(bits, str) or any(bit not in "01" for bit in bits):
                return None
            descending = (kind == "RangeSelectExpression"
                          and str(node.selectionKind).split(".")[-1]
                          == "IndexedDown")
            return (base, node.type.bitWidth,
                    parent_offset + int(bits, 2),
                    not node.type.isFourState, descending)
        except Exception:
            return None

    if expression_kind not in ("ElementSelectExpression", "RangeSelectExpression"):
        return None
    window = member_window(expression)
    if window is None:
        return None
    base, width, offset, two_state, descending = window
    index = {
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": 32,
        "bits": format(offset & ((1 << 32) - 1), "032b"),
    }
    result = {
        "kind": result_kind,
        "span": node_span(sm, expression),
        "width": width,
        "value": _convert_expr(sm, base),
        "index": index,
        "index_signed": False,
        "descending": descending,
    }
    if result_kind == "SelectTarget":
        result["two_state"] = two_state
    return result


def _convert_selected_read(sm, expr, expression_kind):
    if expression_kind == "ElementSelectExpression":
        string_byte = _string_literal_index_value(expr)
        if string_byte is not None:
            width = expr.type.bitWidth
            return signed_metadata({
                "kind": "Literal",
                "span": node_span(sm, expr),
                "width": width,
                "bits": format(string_byte & ((1 << width) - 1),
                               f"0{width}b"),
                "string_literal_index": True,
            }, expr.type)
        assoc_cell = _finite_string_assoc_cell(sm, expr)
        if assoc_cell is not None:
            return {
                "kind": "Ident",
                "span": node_span(sm, expr),
                "width": assoc_cell["width"],
                "name": assoc_cell["name"],
            }
        assoc_cell = _finite_integral_assoc_cell(sm, expr)
        if assoc_cell is not None:
            return {
                "kind": "Ident",
                "span": node_span(sm, expr),
                "width": assoc_cell["width"],
                "name": assoc_cell["name"],
            }
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
        nested_dynamic_array = _fixed_array_nested_dynamic_read(sm, expr)
        if nested_dynamic_array is not None:
            return nested_dynamic_array
        oob = _fixed_array_oob_read(sm, expr)
        if oob is not None:
            width, two_state = oob
            return signed_metadata({
                "kind": "Literal",
                "span": node_span(sm, expr),
                "width": width,
                "bits": ("0" if two_state else "x") * width,
                "unpacked_array_oob_read": True,
            }, expr.type)
    nested_window = _nested_packed_constant_window(sm, expr, "SelectRead")
    if nested_window is not None:
        return nested_window
    packed_array_window = _fixed_array_packed_window(
        sm, expr, "SelectRead")
    if packed_array_window is not None:
        return packed_array_window
    dynamic_packed_array_window = _fixed_array_dynamic_packed_window(
        sm, expr, "SelectRead")
    if dynamic_packed_array_window is not None:
        return dynamic_packed_array_window
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
            if _constant_dimension_selector(expr.left) is None:
                dynamic = _packed_dynamic_indexed_index(
                    sm, source_type, expr.left, expr.type.bitWidth, selection)
                if dynamic is None:
                    normalized = None
                else:
                    converted_index, index_signed, descending = dynamic
                    normalized = (converted_index, index_signed, descending)
            else:
                normalized = _packed_constant_indexed_index(
                    sm, source_type, expr.left, expr.type.bitWidth,
                    selection == "IndexedDown")
        else:
            normalized = None
        if normalized is None:
            return unsupported(sm, expr, expression_kind + ":source-type")
        if len(normalized) == 3:
            converted_index, index_signed, descending = normalized
        else:
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


def _literal_function_return(expression):
    """Recognize a literal-only function return without evaluating code."""
    kind = type(expression).__name__
    if kind in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
        return not getattr(expression, "bad", False)
    if kind == "ConversionExpression":
        return _literal_function_return(getattr(expression, "operand", None))
    if kind == "UnaryExpression":
        op = str(getattr(expression, "op", "")).split(".")[-1]
        return op in ("Plus", "Minus") and _literal_function_return(
            getattr(expression, "operand", None))
    return False


def _literal_function_symbol(subroutine):
    """Whether a function declaration is erased after literal call lowering.

    Input formals are harmless metadata when the complete body returns a
    literal.  Output, inout, and reference formals are retained because a
    call can observe their copy-in/copy-out or aliasing effects even when the
    return expression itself is constant.
    """
    try:
        if (str(getattr(subroutine, "subroutineKind", "")).split(".")[-1]
                != "Function"):
            return False
        if any(str(getattr(argument, "direction", "")).split(".")[-1] != "In"
               for argument in getattr(subroutine, "arguments", [])):
            return False
        body = getattr(subroutine, "body", None)
        returned = (getattr(body, "expr", None)
                    if type(body).__name__ == "ReturnStatement" else None)
        return returned is not None and _literal_function_return(returned)
    except Exception:
        return False


def _literal_function_call(expression):
    """Whether a literal-return function call has only inert literal inputs."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or getattr(expression, "isSystemCall", False)):
            return False
        subroutine = getattr(expression, "subroutine", None)
        formals = list(getattr(subroutine, "arguments", []))
        actuals = list(getattr(expression, "arguments", []))
        if not _literal_function_symbol(subroutine) or len(formals) != len(actuals):
            return False
        return all(_literal_function_return(argument) for argument in actuals)
    except Exception:
        return False


def _literal_real_decimal(expression):
    """Read a source-real literal without going through binary ``float``.

    ``$rtoi`` truncates toward zero. Keeping the decimal spelling until the
    conversion avoids turning a source value such as ``123.9`` into a host
    floating-point approximation, and keeps the admission limited to literal
    operands rather than pretending that real storage is modeled.
    """
    node = expression
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return None
    if type(node).__name__ in ("RealLiteral", "ShortRealLiteral"):
        if getattr(node, "bad", False):
            return None
        try:
            source = str(getattr(node, "syntax", "")).replace("_", "")
            value = Decimal(source)
            return value if value.is_finite() else None
        except (InvalidOperation, ValueError):
            return None
    # `$itor` is exact for a literal integral operand.  Keep this nested
    # conversion narrow: named values, computed expressions, and every other
    # real-producing call still require an opaque real value and stay loud.
    if (type(node).__name__ == "CallExpression"
            and not getattr(node, "bad", False)
            and getattr(node, "isSystemCall", False)
            and getattr(node, "subroutineName", None) == "$itor"):
        try:
            arguments = list(node.arguments)
            if (len(arguments) != 1
                    or not getattr(arguments[0].type, "isIntegral", False)
                    or type(node.type.canonicalType).__name__ != "FloatingType"):
                return None
            integer = _literal_integral_value(arguments[0])
            return Decimal(integer) if integer is not None else None
        except (AttributeError, TypeError, ValueError, InvalidOperation):
            return None
    if type(node).__name__ == "UnaryExpression":
        op = str(getattr(node, "op", "")).split(".")[-1]
        if op not in ("Plus", "Minus", "UnaryPlus", "UnaryMinus"):
            return None
        value = _literal_real_decimal(getattr(node, "operand", None))
        if value is None:
            return None
        return -value if op in ("Minus", "UnaryMinus") else value
    return None


def _bound_real_decimal(expression):
    """Resolve a literal-bound real/shortreal variable at one call site.

    Real storage is deliberately absent from the flat self-check state.  A
    named floating value is nevertheless exact when its declaration
    initializer, or each earlier direct blocking assignment, is a finite
    literal and no such assignment is control-dependent.  The source-order
    check is conservative: a dynamic write, nonblocking write, or assignment
    inside a control shell keeps the ordinary opaque-storage boundary loud.
    """
    direct = _literal_real_decimal(expression)
    if direct is not None:
        return direct
    try:
        node = expression
        while type(node).__name__ == "ConversionExpression":
            node = getattr(node, "operand", None)
            if node is None:
                return None
        if (type(node).__name__ != "NamedValueExpression"
                or getattr(node, "bad", False)):
            return None
        canonical = getattr(getattr(node, "type", None), "canonicalType", None)
        if type(canonical).__name__ != "FloatingType":
            return None
        symbol = getattr(node, "symbol", None)
        if symbol is None:
            return None
        position = getattr(getattr(getattr(node, "sourceRange", None),
                                   "start", None), "offset", None)
        if position is None:
            return None
        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        if instance is None:
            return None
        controls = []
        assignments = []

        def inspect(node):
            kind = type(node).__name__
            if kind in ("ConditionalStatement", "ForLoopStatement",
                        "WhileLoopStatement", "DoWhileLoopStatement",
                        "RepeatLoopStatement", "ForeachLoopStatement",
                        "CaseStatement", "CaseInsideStatement",
                        "CasePatternStatement", "LoopStatement"):
                controls.append(getattr(node, "sourceRange", None))
            elif kind == "AssignmentExpression":
                left = getattr(node, "left", None)
                if (type(left).__name__ == "NamedValueExpression"
                        and getattr(left, "symbol", None) is symbol):
                    assignments.append(node)

        instance.visit(inspect)
        prior = []
        for assignment in assignments:
            start = getattr(getattr(assignment.sourceRange, "start", None), "offset", None)
            end = getattr(getattr(assignment.sourceRange, "end", None), "offset", None)
            if start is None or end is None or start >= position:
                continue
            prior.append(assignment)
            if (assignment.op is not None or assignment.timingControl is not None
                    or getattr(assignment, "isNonBlocking", False)
                    or any(r is not None
                           and r.start.offset <= start and end <= r.end.offset
                           for r in controls)):
                return None
        initializer = getattr(symbol, "initializer", None)
        value = _literal_real_decimal(initializer) if initializer is not None else None
        if initializer is not None and value is None:
            return None
        for assignment in sorted(prior,
                                 key=lambda a: a.sourceRange.start.offset):
            candidate = _literal_real_decimal(getattr(assignment, "right", None))
            if candidate is None:
                return None
            value = candidate
        return value
    except Exception:
        return None


def _rtoi_literal_call(expression):
    """Whether ``$rtoi`` has one finite literal real in value position."""
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$rtoi"):
            return False
        arguments = list(expression.arguments)
        if len(arguments) != 1:
            return False
        value = _literal_real_decimal(arguments[0])
        return (value is not None and getattr(expression.type, "isIntegral", False)
                and getattr(expression.type, "bitWidth", None) == 32)
    except Exception:
        return False


def _itor_literal_call(expression):
    """Whether discarded ``$itor`` has one direct finite integral literal."""
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$itor"):
            return False
        arguments = list(expression.arguments)
        return (len(arguments) == 1
                and type(expression.type.canonicalType).__name__ == "FloatingType"
                and _literal_integral_value(arguments[0]) is not None)
    except Exception:
        return False


def _bitstoreal_literal_call(expression):
    """Whether discarded ``$bitstoreal`` has one known 64-bit literal."""
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$bitstoreal"):
            return False
        arguments = list(expression.arguments)
        return (len(arguments) == 1
                and type(expression.type.canonicalType).__name__ == "FloatingType"
                and getattr(arguments[0].type, "isIntegral", False)
                and getattr(arguments[0].type, "bitWidth", None) == 64
                and _literal_integral_value(arguments[0]) is not None)
    except Exception:
        return False


def _bitstoshortreal_literal_call(expression):
    """Whether discarded ``$bitstoshortreal`` has one known 32-bit literal."""
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$bitstoshortreal"):
            return False
        arguments = list(expression.arguments)
        return (len(arguments) == 1
                and type(expression.type.canonicalType).__name__ == "FloatingType"
                and getattr(arguments[0].type, "isIntegral", False)
                and getattr(arguments[0].type, "bitWidth", None) == 32
                and _literal_integral_value(arguments[0]) is not None)
    except Exception:
        return False


def _convert_rtoi_literal(sm, expression):
    if not _rtoi_literal_call(expression):
        return unsupported(sm, expression, "CallExpression:$rtoi")
    value = _literal_real_decimal(expression.arguments[0])
    truncated = int(value.to_integral_value(rounding=ROUND_DOWN))
    width = expression.type.bitWidth
    if truncated < -(1 << (width - 1)) or truncated >= (1 << (width - 1)):
        return unsupported(sm, expression, "CallExpression:$rtoi:range")
    bits = format(truncated & ((1 << width) - 1), f"0{width}b")
    return signed_metadata({
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": width,
        "bits": bits,
        "rtoi_literal": True,
    }, expression.type)


def _realtobits_literal_call(expression):
    """Whether ``$realtobits`` has a direct finite literal real operand.

    A literal `$itor` conversion is exact, so it joins the direct real-literal
    form without introducing a real storage boundary.
    """
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$realtobits"):
            return False
        arguments = list(expression.arguments)
        if len(arguments) != 1:
            return False
        argument = arguments[0]
        node = argument
        if type(node).__name__ == "UnaryExpression":
            op = str(getattr(node, "op", "")).split(".")[-1]
            if op not in ("Plus", "Minus", "UnaryPlus", "UnaryMinus"):
                return False
            node = getattr(node, "operand", None)
        # Do not strip a conversion shell here: shortreal or an explicit real
        # cast changes the source value before the IEEE-754 bit conversion.
        literal_operand = (type(node).__name__ == "RealLiteral"
                           or type(node).__name__ == "NamedValueExpression")
        itor_operand = (type(node).__name__ == "CallExpression"
                        and not getattr(node, "bad", False)
                        and getattr(node, "isSystemCall", False)
                        and getattr(node, "subroutineName", None) == "$itor")
        return ((literal_operand or itor_operand)
                and not getattr(node, "bad", False)
                and getattr(expression.type, "bitWidth", None) == 64
                and getattr(expression.type, "isIntegral", False)
                and not getattr(expression.type, "isSigned", True)
                and (_literal_real_decimal(argument) is not None
                     or _bound_real_decimal(argument) is not None))
    except Exception:
        return False


def _convert_realtobits_literal(sm, expression):
    if not _realtobits_literal_call(expression):
        return unsupported(sm, expression, "CallExpression:$realtobits")
    value = (_literal_real_decimal(expression.arguments[0])
             if _literal_real_decimal(expression.arguments[0]) is not None
             else _bound_real_decimal(expression.arguments[0]))
    try:
        real_value = float(value)
        if not math.isfinite(real_value):
            return unsupported(sm, expression, "CallExpression:$realtobits:range")
        encoded = struct.unpack(">Q", struct.pack(">d", real_value))[0]
    except (OverflowError, ValueError, struct.error):
        return unsupported(sm, expression, "CallExpression:$realtobits:range")
    return {
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": 64,
        "bits": format(encoded, "064b"),
        "realtobits_literal": True,
    }


def _shortrealtobits_literal_call(expression):
    """Whether ``$shortrealtobits`` has one implicit literal conversion.

    The implicit shell may wrap either a direct real literal or an exact
    literal `$itor` result; all other real-producing expressions stay loud.
    """
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$shortrealtobits"):
            return False
        arguments = list(expression.arguments)
        if len(arguments) != 1:
            return False
        argument = arguments[0]
        if type(argument).__name__ == "ConversionExpression":
            if str(getattr(argument, "conversionKind", "")).split(".")[-1] != "Implicit":
                return False
            node = getattr(argument, "operand", None)
        elif type(argument).__name__ == "NamedValueExpression":
            node = argument
        else:
            return False
        if type(node).__name__ == "UnaryExpression":
            op = str(getattr(node, "op", "")).split(".")[-1]
            if op not in ("Plus", "Minus", "UnaryPlus", "UnaryMinus"):
                return False
            node = getattr(node, "operand", None)
        literal_operand = (type(node).__name__ in
                           ("RealLiteral", "NamedValueExpression"))
        itor_operand = (type(node).__name__ == "CallExpression"
                        and not getattr(node, "bad", False)
                        and getattr(node, "isSystemCall", False)
                        and getattr(node, "subroutineName", None) == "$itor")
        return ((literal_operand or itor_operand)
                and not getattr(node, "bad", False)
                and getattr(expression.type, "bitWidth", None) == 32
                and getattr(expression.type, "isIntegral", False)
                and not getattr(expression.type, "isSigned", True)
                and (_literal_real_decimal(argument) is not None
                     or _bound_real_decimal(argument) is not None))
    except Exception:
        return False


def _convert_shortrealtobits_literal(sm, expression):
    if not _shortrealtobits_literal_call(expression):
        return unsupported(sm, expression, "CallExpression:$shortrealtobits")
    value = (_literal_real_decimal(expression.arguments[0])
             if _literal_real_decimal(expression.arguments[0]) is not None
             else _bound_real_decimal(expression.arguments[0]))
    try:
        real_value = float(value)
        if not math.isfinite(real_value):
            return unsupported(sm, expression, "CallExpression:$shortrealtobits:range")
        encoded = struct.unpack(">I", struct.pack(">f", real_value))[0]
    except (OverflowError, ValueError, struct.error):
        return unsupported(sm, expression, "CallExpression:$shortrealtobits:range")
    return {
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": 32,
        "bits": format(encoded, "032b"),
        "shortrealtobits_literal": True,
    }


def _convert_legacy_call(sm, expression):
    # An empty zero-argument function returns its type's default value.  The
    # declaration has already been erased as metadata; materialize that
    # default at an expression use (all-zero for 2-state, all-x for 4-state).
    try:
        subroutine = expression.subroutine
        body = getattr(subroutine, "body", None)
        body_list = (list(body.list)
                     if type(body).__name__ == "StatementList" else None)
        kind = str(getattr(subroutine, "subroutineKind", "")).split(".")[-1]
        formal_args = list(getattr(subroutine, "arguments", []))
        receiver = getattr(expression, "thisClass", None)
        receiver_type = getattr(getattr(receiver, "type", None), "canonicalType", None)
        opaque_method_call = (
            receiver is not None
            and type(receiver_type).__name__ == "ClassType"
            and getattr(receiver_type, "name", None) == "mailbox"
            and getattr(expression, "subroutineName", None) == "num")
        no_args = (kind == "Function" and list(expression.arguments) == []
                   and formal_args == [] and not opaque_method_call)
        if no_args and body_list == []:
            width, two_state, reason = type_width_2s(expression.type)
            if width is not None and reason is None:
                return signed_metadata({
                    "kind": "Literal", "span": node_span(sm, expression),
                    "width": width,
                    "bits": ("0" if two_state else "x") * width,
                    "empty_function_default": True,
                }, expression.type)
        # A zero-argument function whose body is one literal return has no
        # storage, timing, or call effects.  The return expression has already
        # undergone SystemVerilog's function-result sizing in pyslang, so the
        # converted literal can be used directly at the call site.  Keep this
        # deliberately narrower than general constant-function evaluation:
        # names, operators, nested calls, and multi-statement bodies remain
        # ordinary unsupported calls rather than silently erasing effects.
        if (not opaque_method_call and _literal_function_call(expression)
                and type(body).__name__ == "ReturnStatement"):
            returned = getattr(body, "expr", None)
            if (returned is not None and _literal_function_return(returned)
                    and _case_source_expression_ok(returned)):
                value = convert_expr(sm, returned)
                if (value is not None and value.get("kind") != "Unsupported"
                        and width_of(value) == expression.type.bitWidth):
                    value = signed_metadata(value, expression.type)
                    value["literal_function_return"] = True
                    value["span"] = node_span(sm, expression)
                    return value
    except Exception:
        pass
    mailbox_state = _convert_mailbox_literal_state_call(sm, expression)
    if mailbox_state is not None:
        return mailbox_state
    mailbox_mismatch = _convert_mailbox_type_mismatch_try_get(sm, expression)
    if mailbox_mismatch is not None:
        return mailbox_mismatch
    if (_SYM is None and getattr(expression, "isSystemCall", False)
            and getattr(expression, "subroutineName", "") == "$q_full"):
        value = _q_full_value_call(sm, expression)
        if value is not None:
            return value
    sformatf = _convert_sformatf_call(sm, expression)
    if sformatf is not None:
        return sformatf
    for recognizes, convert in (
            (_time_scale_call, _convert_time_scale_call),
            (_fopen_invalid_mode_call, _convert_fopen_invalid_mode),
            (_fseek_stdout_error_call, _convert_fseek_stdout_error),
            (_ftell_stdout_error_call, _convert_ftell_stdout_error),
            (_plusargs_call, _convert_plusargs_call),
            (_dynamic_cast_call, _convert_dynamic_cast),
            (_coverage_call, _convert_coverage_call),
            (_isunbounded_call, _convert_isunbounded),
            (_array_reduction_index_call, _convert_array_reduction_index),
            (_array_reduction_call, _convert_array_reduction),
            (lambda e: _enum_method_call(e, include_name=True), _convert_enum_method),
            (_clog2_call, _convert_clog2),
            (_dimension_query_call, _convert_dimension_query),
            (_empty_dynamic_bits_query, _convert_empty_dynamic_bits_query),
            (_string_literal_getc_method, _convert_string_literal_getc),
            (_string_literal_compare_method, _convert_string_literal_compare),
            (_string_literal_atoi_method, _convert_string_literal_atoi),
            (_string_literal_radix_method, _convert_string_literal_radix),
            (_string_literal_len_method, _convert_string_literal_len_method),
            (_semaphore_zero_try_get, _convert_semaphore_zero_try_get),
            (_semaphore_literal_try_get, _convert_semaphore_literal_try_get),
            (_dynamic_array_literal_size_method, _convert_dynamic_array_literal_size),
            (_mailbox_empty_try_method, _convert_mailbox_empty_try_method),
            (_event_triggered_false, _convert_event_triggered_false),
            (_mailbox_empty_num_method, _convert_mailbox_empty_num),
            (lambda e: _mailbox_literal_sequence(e) is not None
                       and e.subroutineName == "num",
             _convert_mailbox_literal_num),
            (_queue_empty_pop_method, _convert_queue_empty_pop),
            (_associative_empty_query, _convert_associative_empty_query),
            (_associative_empty_endpoint, _convert_associative_empty_endpoint),
            (_zero_size_method, _convert_zero_size_method),
            (_rtoi_literal_call, _convert_rtoi_literal),
            (_realtobits_literal_call, _convert_realtobits_literal),
            (_shortrealtobits_literal_call, _convert_shortrealtobits_literal),
            (_time_call, _convert_time_call),
            (_stime_call, _convert_stime_call),
            (_signing_call, _convert_signing_call),
            (_bit_query_call, _convert_bit_query)):
        if recognizes(expression):
            return convert(sm, expression)
    return _convert_fixed_bits_query(sm, expression)


def _convert_sformatf_call(sm, expression):
    """Lower the pure one-integral-argument `$sformatf` slice.

    The self-check state represents the resulting text as an ASCII packed
    vector. Keep the format language deliberately small and literal: one
    conversion from the integral display inventory already rendered by the
    self-check tier. Dynamic formats, multiple arguments, aggregate/real
    operands, and every other conversion remain a loud call boundary.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or not getattr(expression, "isSystemCall", False)
                or getattr(expression, "subroutineName", "") != "$sformatf"):
            return None
        args = list(expression.arguments)
        if len(args) != 2:
            return unsupported(sm, expression, "CallExpression:$sformatf:arity")
        format_expr, operand = args
        if (type(format_expr).__name__ != "StringLiteral"
                or getattr(format_expr, "bad", False)
                or _contains_disputed_string_escape(format_expr)):
            return unsupported(sm, expression, "CallExpression:$sformatf:format")
        if format_expr.value not in ("%b", "%B", "%h", "%H",
                                     "%o", "%O", "%d", "%D",
                                     "%c", "%C"):
            return unsupported(sm, expression, "CallExpression:$sformatf:format")
        width, _two_state, reason = type_width_2s(operand.type)
        if width is None or reason is not None or width <= 0:
            return unsupported(sm, expression, "CallExpression:$sformatf:operand")
        if not _case_source_expression_ok(operand):
            return unsupported(sm, expression, "CallExpression:$sformatf:operand")
        converted = convert_expr(sm, operand)
        if (converted is None or converted.get("kind") == "Unsupported"
                or not _case_expression_ok(converted)):
            return unsupported(sm, expression, "CallExpression:$sformatf:operand")
        return {
            "kind": "SFormatF",
            "span": node_span(sm, expression),
            "format": format_expr.value,
            "operand": converted,
            "signed": bool(getattr(operand.type, "isSigned", False)),
        }
    except Exception:
        return unsupported(sm, expression, "CallExpression:$sformatf")


def _fixed_array_packed_window(sm, expression, result_kind):
    """Lower a constant outer slice inside a packed fixed-array cell.

    For ``bit [3:0][7:0] a [0:9]``, ``a[7][3:2]`` is a 16-bit window of the
    ordinary 32-bit cell ``a[7]``.  The existing selected-read/target nodes
    already model a constant bit offset, so normalize the outer packed labels
    to that offset and preserve the source cell as the base value.
    """
    try:
        if type(expression).__name__ != "RangeSelectExpression":
            return None
        if str(expression.selectionKind).split(".")[-1] != "Simple":
            return None
        base_cell = _fixed_array_cell(sm, expression.value)
        if base_cell is None:
            return None
        base_name, base_width, base_two = base_cell
        source_type = expression.value.type.canonicalType
        if type(source_type).__name__ != "PackedArrayType":
            return None
        inner_type = source_type.elementType.canonicalType
        if type(inner_type).__name__ not in ("PackedArrayType",
                                             "PackedStructType",
                                             "PackedUnionType"):
            return None
        element_width = int(inner_type.bitWidth)
        if element_width <= 0:
            return None
        declared_left, declared_right = int(source_type.range.left), int(source_type.range.right)
        left = _constant_dimension_selector(expression.left)
        right = _constant_dimension_selector(expression.right)
        low, high = min(declared_left, declared_right), max(declared_left, declared_right)
        if (left is None or right is None or left < low or left > high
                or right < low or right > high or left < right
                or expression.type.bitWidth != (left - right + 1) * element_width):
            return None
        offset = ((right - declared_right) if declared_left > declared_right
                  else (declared_right - right)) * element_width
        if offset < 0 or offset + expression.type.bitWidth > base_width:
            return None
        index = {"kind": "Literal", "span": node_span(sm, expression),
                 "width": 32, "bits": format(offset, "032b")}
        base = {"kind": "Ident", "span": node_span(sm, expression.value),
                "width": base_width, "name": base_name}
        result = {"kind": result_kind, "span": node_span(sm, expression),
                  "width": expression.type.bitWidth, "value": base,
                  "index": index, "index_signed": False,
                  "descending": False}
        if result_kind == "SelectTarget":
            result["two_state"] = bool(base_two)
        return result
    except Exception:
        return None


def _fixed_array_dynamic_packed_window(sm, expression, result_kind):
    """Lower a dynamic indexed slice of a packed fixed-array cell.

    A cell such as ``joe[7]`` in ``bit [3:0][7:0] joe [0:9]`` is stored as
    one flat 32-bit vector.  The indexed-select base is expressed in the
    outer packed-array labels, so a runtime base must be scaled by the inner
    element width before it reaches the selected-read/write evaluator.  This
    deliberately keeps the admitted shape to descending packed ranges and a
    pure integral base; scalar packed vectors already use the ordinary path.
    """
    try:
        if type(expression).__name__ != "RangeSelectExpression":
            return None
        selection = str(expression.selectionKind).split(".")[-1]
        if selection not in ("IndexedUp", "IndexedDown"):
            return None
        base_cell = _fixed_array_cell(sm, expression.value)
        if base_cell is None:
            return None
        base_name, base_width, base_two = base_cell
        source_type = expression.value.type.canonicalType
        if type(source_type).__name__ != "PackedArrayType":
            return None
        inner_type = source_type.elementType.canonicalType
        if type(inner_type).__name__ not in ("PackedArrayType",
                                             "PackedStructType",
                                             "PackedUnionType"):
            return None
        declared_left = int(source_type.range.left)
        declared_right = int(source_type.range.right)
        if declared_left <= declared_right:
            return None
        element_width = int(inner_type.bitWidth)
        width = int(expression.type.bitWidth)
        if (element_width <= 0 or width <= 0
                or width % element_width != 0
                or width > base_width):
            return None
        count = width // element_width
        index = expression.left
        index_width, _index_two, index_reason = type_width_2s(index.type)
        if (index_width is None or index_reason is not None
                or not _case_source_expression_ok(index)):
            return None
        converted_index = _convert_expr(sm, index)
        if (converted_index is None or not _case_expression_ok(converted_index)
                or width_of(converted_index) != index_width):
            return None

        span = node_span(sm, expression)

        def literal(value):
            mask = (1 << index_width) - 1
            return {"kind": "Literal", "span": span, "width": index_width,
                    "bits": format(value & mask, f"0{index_width}b")}

        def binary(op, left, right):
            return {"kind": "Binary", "span": span, "width": index_width,
                    "op": op, "left": left, "right": right}

        # Normalize the outer packed label to its cell's LSB offset.  The
        # range is descending, so label ``right`` starts at offset zero.
        normalized = converted_index
        if declared_right:
            normalized = binary("-", normalized, literal(declared_right))
        if selection == "IndexedDown":
            normalized = binary("+", normalized, literal(1))
        normalized = binary("*", normalized, literal(element_width))
        if selection == "IndexedDown":
            normalized = binary("-", normalized, literal(1))
        result = {"kind": result_kind, "span": span, "width": width,
                  "value": {"kind": "Ident", "span": node_span(sm, expression.value),
                            "width": base_width, "name": base_name},
                  "index": normalized,
                  "index_signed": bool(index.type.isSigned),
                  "descending": selection == "IndexedDown"}
        if result_kind == "SelectTarget":
            result["two_state"] = bool(base_two)
        return result
    except Exception:
        return None


def _nested_packed_constant_window(sm, expression, result_kind):
    """Flatten constant selections through nested packed dimensions.

    A packed vector such as ``logic [1:0][3:0] value`` is one flat LVec.
    When every element/range label is constant, compose each declared-range
    offset and reuse the ordinary selected-read/target node against the root
    vector.  Dynamic labels and aggregate/member receivers stay on their
    existing loud boundaries.
    """
    try:
        current = expression
        offset = 0
        selections = 0
        while type(current).__name__ in ("ElementSelectExpression",
                                         "RangeSelectExpression"):
            selections += 1
            source = getattr(current, "value", None)
            source_type = getattr(source, "type", None)
            canonical = getattr(source_type, "canonicalType", source_type)
            if type(canonical).__name__ != "PackedArrayType":
                return None
            kind = type(current).__name__
            if kind == "ElementSelectExpression":
                normalized = _packed_constant_index(sm, source_type,
                                                    current.selector)
            else:
                selection = str(current.selectionKind).split(".")[-1]
                if selection == "Simple":
                    normalized = _packed_constant_simple_index(
                        sm, source_type, current.left, current.right,
                        current.type.bitWidth)
                elif selection in ("IndexedUp", "IndexedDown"):
                    normalized = _packed_constant_indexed_index(
                        sm, source_type, current.left, current.type.bitWidth,
                        selection == "IndexedDown")
                else:
                    normalized = None
            if normalized is None:
                return None
            literal, _ = normalized
            bits = literal.get("bits")
            if not isinstance(bits, str) or any(bit not in "01" for bit in bits):
                return None
            offset += int(bits, 2)
            current = source
        if selections < 2:
            return None
        if not _storage_expression(current):
            return None
        root_width, _root_two, root_reason = type_width_2s(current.type)
        if root_width is None or root_reason is not None:
            return None
        width = expression.type.bitWidth
        if width <= 0 or offset < 0 or offset + width > root_width:
            return None
        base = convert_expr(sm, current)
        if not _case_expression_ok(base):
            return None
        index = {"kind": "Literal", "span": node_span(sm, expression),
                 "width": 32, "bits": format(offset, "032b")}
        result = {"kind": result_kind, "span": node_span(sm, expression),
                  "width": width, "value": base, "index": index,
                  "index_signed": False, "descending": False}
        if result_kind == "SelectTarget":
            result["two_state"] = not expression.type.isFourState
        return result
    except Exception:
        return None


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


def _floating_literal(expr):
    """Return whether *expr* is a side-effect-free real literal.

    Floating storage is intentionally opaque in the self-check state.  A
    blocking write of a literal therefore has no modeled state to update and
    can be erased, while names, calls, and arithmetic remain loud at their
    existing expression boundaries.  Keep the small unary/conversion shells
    that pyslang puts around signed and context-converted literals.
    """
    node = expr
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return False
    if type(node).__name__ == "RealLiteral":
        return not getattr(node, "bad", False)
    if type(node).__name__ == "UnaryExpression":
        op = str(getattr(node, "op", "")).split(".")[-1]
        if op not in ("Plus", "Minus"):
            return False
        return _floating_literal(getattr(node, "operand", None))
    return False


def _integral_literal_source(expr):
    """Whether an expression is syntactically a pure integral literal.

    Elaboration can fold genvar and parameter references into ``Literal``
    envelope nodes. Continuous-driver lowering must not mistake those
    source-dependent values for a literal driver, because the source still
    requires continuous evaluation.
    """
    node = expr
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return False
    if type(node).__name__ in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
        return not getattr(node, "bad", False)
    if type(node).__name__ == "UnaryExpression":
        op = str(getattr(node, "op", "")).split(".")[-1]
        return op in ("Plus", "Minus") and _integral_literal_source(
            getattr(node, "operand", None))
    return False


def _constant_integral_source(sm, expr):
    """Return a binder-folded literal for a pure integral source expression.

    This extends the direct-literal driver path only when pyslang has already
    proved the complete expression at elaboration. Dynamic reads and effectful
    calls therefore remain on the live continuous-driver boundary.
    """
    try:
        if (_integral_literal_source(expr)
                or not _all_literal_integral_tree(expr)
                or not _case_source_expression_ok(expr)):
            return None
        literal = const_literal(sm, expr)
        if literal is None:
            literal = _evaluate_unsigned_literal(sm, expr)
        if literal is None or not expr.type.isIntegral:
            return None
        return literal
    except Exception:
        return None


def _all_literal_integral_tree(expr):
    """Reject names, calls, and elaboration-bound references before folding."""
    allowed = {"IntegerLiteral", "UnbasedUnsizedIntegerLiteral",
               "ConversionExpression", "UnaryExpression", "BinaryExpression"}
    try:
        valid = True
        def inspect(node):
            nonlocal valid
            valid = valid and type(node).__name__ in allowed
        expr.visit(inspect)
        return valid
    except Exception:
        return False


def _evaluate_unsigned_literal(sm, expr):
    """Evaluate a small all-literal unsigned integral expression tree.

    This is deliberately separate from the general expression converter: only
    known 0/1 literals, unsigned operands, and side-effect-free arithmetic or
    bitwise operators are folded into a continuous driver's time-zero value.
    """
    try:
        if getattr(expr.type, "isSigned", True) or not expr.type.isIntegral:
            return None
        width = expr.type.bitWidth
        if width <= 0 or width > 1024:
            return None
        kind = type(expr).__name__
        value = None
        if kind in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
            bits = svint_bits(expr.value)
            if any(bit not in "01" for bit in bits):
                return None
            value = int(bits, 2)
        elif kind == "ConversionExpression":
            operand = _literal_value(_evaluate_unsigned_literal(sm, expr.operand))
            value = int(operand["bits"], 2) if operand is not None else None
            if value is None:
                return None
        elif kind == "UnaryExpression":
            operand = _evaluate_unsigned_literal(sm, expr.operand)
            if operand is None:
                return None
            value = int(operand["bits"], 2)
            op = str(expr.op).split(".")[-1]
            if op == "Plus":
                pass
            elif op == "Minus":
                value = -value
            elif op == "BitwiseNot":
                value = ~value
            else:
                return None
        elif kind == "BinaryExpression":
            left = _evaluate_unsigned_literal(sm, expr.left)
            right = _evaluate_unsigned_literal(sm, expr.right)
            if left is None or right is None:
                return None
            a, b = int(left["bits"], 2), int(right["bits"], 2)
            op = str(expr.op).split(".")[-1]
            value = {"Add": a + b, "Subtract": a - b,
                     "Multiply": a * b, "BitwiseAnd": a & b,
                     "BitwiseOr": a | b, "BitwiseXor": a ^ b}.get(op)
            if value is None:
                return None
        else:
            return None
        mask = (1 << width) - 1
        return {"kind": "Literal", "span": node_span(sm, expr),
                "width": width, "bits": format(value & mask, f"0{width}b"),
                "constant_integral_source": True}
    except Exception:
        return None


def _literal_value(node):
    if not isinstance(node, dict) or node.get("kind") != "Literal":
        return None
    bits = node.get("bits")
    return node if isinstance(bits, str) and bits and all(bit in "01" for bit in bits) else None


def _continuous_bound_literal(sm, expression):
    """Return a literal RHS when a net driver reads an immutable literal var."""
    try:
        if type(expression).__name__ != "NamedValueExpression":
            return None
        symbol = getattr(expression, "symbol", None)
        if symbol is None or str(getattr(symbol, "kind", "")).split(".")[-1] != "Variable":
            return None
        initializer = getattr(symbol, "initializer", None)
        if initializer is None or not _integral_literal_source(initializer):
            return None
        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        if instance is None:
            return None
        writes = []
        def inspect(node):
            if type(node).__name__ != "AssignmentExpression":
                return
            left = getattr(node, "left", None)
            if (type(left).__name__ == "NamedValueExpression"
                    and getattr(left, "symbol", None) is symbol):
                writes.append(node)
        instance.visit(inspect)
        if writes:
            return None
        value = convert_expr(sm, initializer)
        if value is None or value.get("kind") == "Unsupported":
            return None
        return value
    except Exception:
        return None


def _continuous_history_literal(sm, expression):
    """Return a literal for a source variable assigned once at time zero.

    A continuous driver normally needs the scheduler because its RHS can
    change after elaboration.  The self-check surface can fold the narrower
    shape where a module variable has one direct blocking literal assignment
    in an initial block and no declaration initializer or other writes.  The
    syntax-parent check excludes control-dependent, loop, task, and function
    writes; all remaining driver forms stay on the live boundary.
    """
    try:
        node = expression
        if type(node).__name__ != "NamedValueExpression":
            return None
        symbol = getattr(node, "symbol", None)
        if (symbol is None
                or str(getattr(symbol, "kind", "")).split(".")[-1] != "Variable"
                or getattr(symbol, "initializer", None) is not None):
            return None
        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        if instance is None:
            return None
        writes = []
        invalid = False

        def direct_initial_write(assignment):
            syntax = getattr(assignment, "syntax", None)
            saw_initial = False
            allowed = {
                "SyntaxKind.AssignmentExpression",
                "SyntaxKind.ExpressionStatement",
                "SyntaxKind.SequentialBlockStatement",
                "SyntaxKind.InitialBlock",
                "SyntaxKind.ModuleDeclaration",
            }
            while syntax is not None:
                kind = str(getattr(syntax, "kind", ""))
                if kind not in allowed:
                    return False
                saw_initial = saw_initial or kind == "SyntaxKind.InitialBlock"
                syntax = getattr(syntax, "parent", None)
            return saw_initial

        def inspect(node):
            nonlocal invalid
            if type(node).__name__ != "AssignmentExpression":
                return
            left = getattr(node, "left", None)
            if left is None:
                return
            references = []
            def inspect_left(child):
                if (type(child).__name__ in
                        ("NamedValueExpression", "HierarchicalValueExpression")
                        and getattr(child, "symbol", None) is symbol):
                    references.append(child)
            left.visit(inspect_left)
            if not references:
                return
            if (len(references) != 1
                    or references[0] is not left
                    or getattr(node, "op", None) is not None
                    or getattr(node, "timingControl", None) is not None
                    or getattr(node, "isNonBlocking", False)
                    or not direct_initial_write(node)):
                invalid = True
                return
            writes.append(node)

        instance.visit(inspect)
        if invalid or len(writes) != 1:
            return None
        value = writes[0].right
        if not _integral_literal_source(value):
            return None
        converted = convert_expr(sm, value)
        if (converted is None or converted.get("kind") != "Literal"
                or not _case_expression_ok(converted)):
            return None
        return converted
    except Exception:
        return None


def _continuous_static_value(sm, expression):
    """Fold an admitted once-assigned literal source of a continuous driver.

    A selected read such as ``data[3:0]`` is also source-pure when ``data``
    has exactly one direct blocking literal write in an ``initial`` block.
    A conditional with literal arms is source-pure when its condition has the
    same single-write or declaration-initializer history. Snapshotting these
    fixed values lets the existing literal net-resolution path handle
    overlapping drivers without inventing a live driver store. Dynamic
    selectors, aliases, unknown conditions, and every source with more than
    one write stay on the scheduler-owned boundary.
    """
    try:
        if _integral_literal_source(expression):
            value = convert_expr(sm, expression)
            if isinstance(value, dict) and value.get("kind") == "Literal":
                return value
        if type(expression).__name__ == "NamedValueExpression":
            value = _continuous_history_literal(sm, expression)
            return value if value is not None else _continuous_bound_literal(sm, expression)
        if type(expression).__name__ == "ConditionalExpression":
            conditions = list(getattr(expression, "conditions", []))
            if len(conditions) != 1 or getattr(conditions[0], "pattern", None) is not None:
                return None
            condition = _continuous_static_value(sm, conditions[0].expr)
            when_true = _continuous_static_value(sm, expression.left)
            when_false = _continuous_static_value(sm, expression.right)
            if (condition is None or when_true is None or when_false is None
                    or condition.get("kind") != "Literal"
                    or when_true.get("kind") != "Literal"
                    or when_false.get("kind") != "Literal"):
                return None
            condition_bits = condition.get("bits")
            if (not isinstance(condition_bits, str)
                    or not condition_bits
                    or any(bit not in "01" for bit in condition_bits)):
                return None
            selected = when_true if "1" in condition_bits else when_false
            width = getattr(expression.type, "bitWidth", None)
            if selected.get("width") != width:
                return None
            return selected
        if type(expression).__name__ not in (
                "ElementSelectExpression", "RangeSelectExpression"):
            return None
        base = getattr(expression, "value", None)
        if type(base).__name__ != "NamedValueExpression":
            return None
        source = _continuous_history_literal(sm, base)
        if source is None:
            source = _continuous_bound_literal(sm, base)
        if source is None:
            return None
        target, admitted = legacy_blocking_target(sm, expression)
        if (not admitted or target.get("kind") != "SelectTarget"
                or target.get("value", {}).get("kind") != "Ident"):
            return None
        source_name = _array_storage_name(getattr(base, "symbol", None))
        if source_name is None or target["value"].get("name") != source_name:
            return None
        index = target.get("index")
        width = target.get("width")
        bits = index.get("bits") if isinstance(index, dict) else None
        if (not isinstance(width, int) or width <= 0
                or not isinstance(bits, str) or not bits
                or any(bit not in "01" for bit in bits)):
            return None
        position = int(bits, 2)
        low = position - width + 1 if target.get("descending") else position
        source_width = source.get("width")
        source_bits = source.get("bits")
        if (not isinstance(source_width, int)
                or not isinstance(source_bits, str)
                or len(source_bits) != source_width
                or low < 0 or low + width > source_width):
            return None
        # Envelope literals are MSB-first while the evaluator stores vectors
        # LSB-first.  Preserve the selected read's source order by extracting
        # the low-offset window and rendering it back in envelope order.
        selected = list(reversed(source_bits))[low:low + width]
        result = dict(source)
        result["span"] = node_span(sm, expression)
        result["width"] = width
        result["bits"] = "".join(reversed(selected))
        return result
    except Exception:
        return None


_PURE_FLOATING_CALLS = {
    "$itor", "$bitstoreal", "$bitstoshortreal", "$sqrt", "$pow",
    "$floor", "$ceil", "$ln", "$log10", "$exp", "$sin", "$cos",
    "$tan", "$asin", "$acos", "$atan", "$atan2", "$hypot", "$sinh",
    "$cosh", "$tanh", "$asinh", "$acosh", "$atanh",
}


def _floating_pure_call(expr):
    """Whether a real-valued system call has no operand side effects.

    Real storage is opaque in the legacy state, so a pure mathematical result
    can be discarded at a blocking write.  Keep the check structural and
    conservative: only the listed IEEE math/conversion calls are admitted,
    and every argument must contain literals, reads, conversions, and pure
    operators only.
    """
    try:
        if (type(expr).__name__ != "CallExpression" or getattr(expr, "bad", False)
                or not expr.isSystemCall
                or expr.subroutineName not in _PURE_FLOATING_CALLS):
            return False
        pure = True

        def inspect(node):
            nonlocal pure
            kind = type(node).__name__
            if kind == "CallExpression":
                pure = pure and _floating_pure_call(node)
                return VisitAction.Skip
            if kind == "UnaryExpression":
                op = str(getattr(node, "op", None)).split(".")[-1]
                pure = pure and op not in (
                    "Preincrement", "Postincrement", "Predecrement",
                    "Postdecrement")
            elif kind not in (
                    "RealLiteral", "IntegerLiteral", "UnbasedUnsizedIntegerLiteral",
                    "TimeLiteral", "NamedValueExpression", "ConversionExpression",
                    "UnaryExpression", "BinaryExpression", "ConditionalExpression",
                    "ConcatenationExpression", "MinTypMaxExpression"):
                pure = False

        for argument in expr.arguments:
            argument.visit(inspect)
        return pure
    except Exception:
        return False


def _null_literal(expr):
    """Whether pyslang's conversion shell contains the null literal."""
    node = expr
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return False
    return type(node).__name__ == "NullLiteral"


def _string_literal_write(expr):
    """Whether *expr* is a pure literal string or literal-only concatenation.

    A string has no flat self-check slot.  A RHS made solely from string
    literals therefore cannot observe or change modeled state; calls,
    variables, and replications remain outside this erased slice.
    """
    node = expr
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return False
    if type(node).__name__ == "StringLiteral":
        return not getattr(node, "bad", False)
    if type(node).__name__ == "ReplicationExpression":
        count = getattr(node, "count", None)
        while type(count).__name__ == "ConversionExpression":
            count = getattr(count, "operand", None)
            if count is None:
                return False
        if (type(count).__name__ != "IntegerLiteral"
                or getattr(count, "bad", False)
                or getattr(count, "value", -1) < 0):
            return False
        return _string_literal_write(getattr(node, "concat", None))
    if type(node).__name__ != "ConcatenationExpression":
        return False
    try:
        operands = list(node.operands)
    except Exception:
        return False
    return bool(operands) and all(_string_literal_write(operand)
                                  for operand in operands)


def _empty_queue_literal(expr):
    """Whether *expr* is the zero-item queue literal ``{}``."""
    node = expr
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return False
    if type(node).__name__ != "ConcatenationExpression":
        return False
    try:
        return len(list(node.operands)) == 0
    except Exception:
        return False


def _queue_literal_element(expr):
    """Whether an expression is a scalar literal usable in a queue write."""
    node = expr
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return False
    return type(node).__name__ in (
        "IntegerLiteral", "UnbasedUnsizedIntegerLiteral", "StringLiteral",
        "NullLiteral", "RealLiteral") and not getattr(node, "bad", False)


def _queue_literal_write_noop(expression):
    """Recognize an unobserved blocking write of literal-only queue data.

    Queue storage is intentionally outside the flat self-check state.  A
    literal-only write whose queue name is never subsequently read or used has
    no observable effect, so it can be erased.  The source-occurrence check
    keeps every element/method/read use on the ordinary loud boundary.
    """
    try:
        if (type(expression).__name__ != "AssignmentExpression"
                or expression.op is not None or expression.timingControl is not None
                or expression.isNonBlocking
                or type(expression.left).__name__ != "NamedValueExpression"
                or type(expression.left.type.canonicalType).__name__ != "QueueType"):
            return False
        rhs = expression.right
        while type(rhs).__name__ == "ConversionExpression":
            rhs = getattr(rhs, "operand", None)
            if rhs is None:
                return False

        def literal_tree(node):
            while type(node).__name__ == "ConversionExpression":
                node = getattr(node, "operand", None)
                if node is None:
                    return False
            kind = type(node).__name__
            if kind in ("ConcatenationExpression", "AssignmentPatternExpression"):
                try:
                    operands = list(node.operands)
                except Exception:
                    return False
                return bool(operands) and all(literal_tree(item) for item in operands)
            if kind == "ReplicationExpression":
                count = getattr(node, "count", None)
                while type(count).__name__ == "ConversionExpression":
                    count = getattr(count, "operand", None)
                    if count is None:
                        return False
                return (_literal_integral_value(count) is not None
                        and _literal_integral_value(count) >= 0
                        and literal_tree(getattr(node, "concat", None)))
            return _queue_literal_element(node)

        if not literal_tree(rhs):
            return False
        name = getattr(expression.left.symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if not name or not source:
            return False
        occurrences = list(re.finditer(r"(?<![A-Za-z0-9_$])" + re.escape(name)
                                       + r"(?![A-Za-z0-9_$])", source))
        assignment_seen = False
        for match in occurrences:
            tail = source[match.end():].lstrip()
            if tail.startswith("[$]") or tail.startswith(";"):
                continue  # declaration-only occurrence
            if tail.startswith("="):
                assignment_seen = True
                continue
            return False
        return assignment_seen
    except Exception:
        return False


def _zero_size_method(expression):
    """Recognize a zero-valued ``size``/``len`` query on inert storage.

    The flat self-check state has no queue or dynamic-array object. An
    uninitialized aggregates and strings are nevertheless defined to have
    zero size. Every later source occurrence of the receiver must be this
    same read-only method; pushes, assignments, and other observations stay
    loud.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName not in ("size", "len")):
            return False
        arguments = list(expression.arguments)
        if len(arguments) != 1 or type(arguments[0]).__name__ != "NamedValueExpression":
            return False
        receiver = arguments[0]
        symbol = receiver.symbol
        canonical = type(receiver.type.canonicalType).__name__
        method = expression.subroutineName
        valid = ((canonical in ("QueueType", "DynamicArrayType") and method == "size")
                 or (canonical == "StringType" and method == "len"))
        if not valid:
            return False
        initializer = getattr(symbol, "initializer", None)
        if (initializer is not None
                and not (canonical == "QueueType"
                         and _empty_queue_literal(initializer))):
            return False
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        code_source = _sv_code_source(source)
        occurrences = list(re.finditer(r"(?<![A-Za-z0-9_$])" + re.escape(name)
                                      + r"(?![A-Za-z0-9_$])", code_source))
        if not occurrences:
            return False
        suffix = "." + method
        def inert_occurrence(match):
            tail = code_source[match.end():].lstrip()
            if tail.startswith(suffix):
                return True
            if canonical in ("QueueType", "DynamicArrayType"):
                if re.match(r"\.delete\s*\(\s*\)", tail):
                    return True
                if canonical == "QueueType" and re.match(
                        r"\.(?:pop_front|pop_back)\s*\(\s*\)", tail):
                    return True
                return (re.match(r"=\s*\{\s*\}", tail) is not None
                        or (canonical == "DynamicArrayType" and
                            re.match(r"=\s*new\s*\[\s*0\s*\]", tail)
                            is not None))
            return re.match(r'=\s*""', tail) is not None
        return all(inert_occurrence(m) for m in occurrences[1:])
    except Exception:
        return False


def _queue_empty_pop_method(expression, allow_struct=False):
    """Recognize a zero-argument pop on a source-pure empty queue.

    IEEE 1800-2023 §7.10.2.4–7.10.2.5 returns the element type's default
    when ``pop_front``/``pop_back`` is applied to an empty queue, and leaves
    that queue empty.  The self-check state has no queue object, so admit only
    an uninitialized or empty-literal queue whose later source uses are the
    corresponding empty pop and/or ``size()`` queries.  Any push, alias, or
    nonempty/dynamic operation remains loud.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName not in ("pop_front", "pop_back")
                or len(expression.arguments) != 1):
            return False
        receiver = expression.arguments[0]
        if (type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)):
            return False
        canonical = type(receiver.type.canonicalType).__name__
        if canonical != "QueueType":
            return False
        symbol = getattr(receiver, "symbol", None)
        initializer = getattr(symbol, "initializer", None)
        if initializer is not None and not _empty_queue_literal(initializer):
            return False
        width, _two_state, reason = type_width_2s(expression.type)
        if width is None or reason is not None:
            if not allow_struct:
                return False
            aggregate = expression.type.canonicalType
            if (type(aggregate).__name__ != "UnpackedStructType"
                    or _unpacked_struct_field_cells("$queue", aggregate, None) is None):
                return False
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if not name or not source:
            return False
        code_source = _sv_code_source(source)
        occurrences = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", code_source))
        if not occurrences:
            return False
        for occurrence in occurrences[1:]:
            tail = code_source[occurrence.end():].lstrip()
            if re.match(r"\.(?:pop_front|pop_back|size)\s*\(\s*\)", tail):
                continue
            return False
        return True
    except Exception:
        return False


def _empty_aggregate_delete_method(expression):
    """Recognize ``delete()`` on source-pure empty queue/dynamic storage.

    Queue ``delete`` is a no-op for an already empty queue.  An uninitialized
    dynamic array is likewise already empty, so deleting it changes no
    represented state.  Keep the receiver's complete source history limited
    to the delete and zero-size queries; initialized, populated, aliased, or
    effectful aggregate operations remain on the loud call boundary.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "delete"
                or len(expression.arguments) != 1):
            return False
        receiver = expression.arguments[0]
        if (type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)):
            return False
        canonical = type(receiver.type.canonicalType).__name__
        if canonical not in ("QueueType", "DynamicArrayType"):
            return False
        symbol = getattr(receiver, "symbol", None)
        initializer = getattr(symbol, "initializer", None)
        if canonical == "QueueType":
            if initializer is not None and not _empty_queue_literal(initializer):
                return False
        elif initializer is not None:
            return False
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if not name or not source:
            return False
        code_source = _sv_code_source(source)
        occurrences = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", code_source))
        if not occurrences:
            return False
        for occurrence in occurrences[1:]:
            tail = code_source[occurrence.end():].lstrip()
            if re.match(r"\.delete\s*\(\s*\)", tail):
                continue
            if re.match(r"\.size\s*\(\s*\)", tail):
                continue
            if (canonical == "QueueType"
                    and re.match(r"\.(?:pop_front|pop_back)\s*\(\s*\)", tail)):
                continue
            return False
        return True
    except Exception:
        return False


def _convert_queue_empty_pop(sm, expression):
    if not _queue_empty_pop_method(expression):
        return unsupported(sm, expression, "CallExpression:queue-empty-pop")
    width, two_state, reason = type_width_2s(expression.type)
    if width is None or reason is not None:
        return unsupported(sm, expression, "CallExpression:queue-empty-pop-type")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": width,
        "bits": ("0" if two_state else "x") * width,
        "queue_empty_pop": expression.subroutineName,
    }, expression.type)


def _queue_empty_pop_struct_assignment(sm, expr):
    """Lower an empty queue pop into the destination's flattened struct cells.

    An empty queue returns the default value of its element type.  The legacy
    state represents integral-only unpacked structs as one scalar/vector cell
    per field, so a direct whole-struct assignment can use the same lowering
    as an out-of-bounds struct read.  Queue mutations, aliases, aggregate
    fields, and nonempty queues remain outside this representation.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or type(expr.right).__name__ != "CallExpression"):
            return None
        if not _queue_empty_pop_method(expr.right, allow_struct=True):
            return None
        lhs_path = _unpacked_struct_path(expr.left)
        if lhs_path is None:
            return None
        lhs_name, lhs_type = lhs_path
        rhs_type = expr.right.type.canonicalType
        if (type(lhs_type).__name__ != "UnpackedStructType"
                or type(rhs_type).__name__ != "UnpackedStructType"):
            return None
        lhs_cells = _unpacked_struct_field_cells(lhs_name, lhs_type,
                                                 node_span(sm, expr))
        values = _unpacked_struct_oob_defaults(
            sm, "$queue", rhs_type, node_span(sm, expr))
        if (lhs_cells is None or values is None
                or len(lhs_cells) != len(values)):
            return None
        if any(lwidth != vwidth for (_lname, lwidth, _linit, _ltype),
               (_vname, vwidth, _value, _vtype) in zip(lhs_cells, values)):
            return None
        stmts = []
        for (name, width, _init, ltype), (_vname, _vwidth, value, _vtype) in zip(
                lhs_cells, values):
            if not ltype.isFourState:
                value = squash2_wrap(value, width)
            stmts.append({
                "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                "span": node_span(sm, expr),
                "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                           "width": width, "name": name},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expr), "stmts": stmts,
                "queue_empty_struct_pop_lowered": True}
    except Exception:
        return None


def _associative_empty_query(expression):
    """Recognize ``num()``/``size()`` on an untouched 2-state assoc array."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName not in ("num", "size")
                or len(expression.arguments) != 1):
            return False
        receiver = expression.arguments[0]
        if (type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)
                or receiver.type.isFourState
                or type(receiver.type.canonicalType).__name__ != "AssociativeArrayType"):
            return False
        symbol = getattr(receiver, "symbol", None)
        if getattr(symbol, "initializer", None) is not None:
            return False
        width, _two_state, reason = type_width_2s(expression.type)
        if width is None or reason is not None:
            return False
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if not name or not source:
            return False
        code_source = _sv_code_source(source)
        occurrences = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", code_source))
        if not occurrences:
            return False
        for occurrence in occurrences[1:]:
            tail = code_source[occurrence.end():].lstrip()
            if (re.match(r"\.(?:num|size)\s*\(\s*\)", tail)
                    or re.match(r"\.delete\s*\(", tail)):
                continue
            return False
        return True
    except Exception:
        return False


def _associative_empty_delete_method(expression):
    """Recognize a discarded delete on an untouched empty assoc array."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "delete"
                or len(expression.arguments) not in (1, 2)):
            return False
        receiver = expression.arguments[0]
        if (type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)
                or receiver.type.isFourState
                or type(receiver.type.canonicalType).__name__ !=
                   "AssociativeArrayType"):
            return False
        if len(expression.arguments) == 2:
            key = expression.arguments[1]
            key_type = getattr(key.type, "canonicalType", key.type)
            if (getattr(key, "bad", False)
                    or (type(key_type).__name__ != "StringType"
                        and not getattr(key.type, "isIntegral", False))
                    or not _case_source_expression_ok(key)):
                return False
        symbol = getattr(receiver, "symbol", None)
        if getattr(symbol, "initializer", None) is not None:
            return False
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if not name or not source:
            return False
        code_source = _sv_code_source(source)
        occurrences = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", code_source))
        if not occurrences:
            return False
        for occurrence in occurrences[1:]:
            tail = code_source[occurrence.end():].lstrip()
            if (re.match(r"\.delete\s*\(", tail)
                    or re.match(r"\.(?:num|size)\s*\(\s*\)", tail)):
                continue
            return False
        return True
    except Exception:
        return False


def _convert_associative_empty_query(sm, expression):
    if not _associative_empty_query(expression):
        return unsupported(sm, expression, "CallExpression:associative-empty-query")
    width, _two_state, reason = type_width_2s(expression.type)
    if width is None or reason is not None:
        return unsupported(sm, expression, "CallExpression:associative-empty-query-type")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": width, "bits": "0" * width,
        "associative_empty_query": expression.subroutineName,
    }, expression.type)


def _associative_empty_endpoint(expression):
    """Recognize ``first(index)``/``last(index)`` on an empty assoc array.

    IEEE 1800-2023 §7.9.4--7.9.5 returns zero when no element exists.  The
    index argument is an output in the non-empty case, so this source slice
    admits only a direct named variable and deliberately does not model any
    index expression effects.  The array itself has no runtime slot in the
    flat self-check state; keep the admission source-pure by allowing only
    the same empty endpoint queries after the declaration.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName not in ("first", "last")
                or len(expression.arguments) != 2):
            return False
        receiver, index = expression.arguments
        if (type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)
                or receiver.type.isFourState
                or type(receiver.type.canonicalType).__name__ != "AssociativeArrayType"):
            return False
        if (type(index).__name__ != "NamedValueExpression"
                or getattr(index, "bad", False)):
            return False
        index_type = getattr(index.type, "canonicalType", index.type)
        if (type(index_type).__name__ != "StringType"
                and not getattr(index.type, "isIntegral", False)):
            return False
        symbol = getattr(receiver, "symbol", None)
        if getattr(symbol, "initializer", None) is not None:
            return False
        width, _two_state, reason = type_width_2s(expression.type)
        if (width != 32 or reason is not None
                or not getattr(expression.type, "isIntegral", False)
                or not getattr(expression.type, "isSigned", False)):
            return False
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if not name or not source:
            return False
        code_source = _sv_code_source(source)
        occurrences = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", code_source))
        if not occurrences:
            return False
        for occurrence in occurrences[1:]:
            tail = code_source[occurrence.end():].lstrip()
            if re.match(r"\.(?:first|last)\s*\(", tail):
                continue
            return False
        return True
    except Exception:
        return False


def _convert_associative_empty_endpoint(sm, expression):
    if not _associative_empty_endpoint(expression):
        return unsupported(sm, expression, "CallExpression:associative-empty-endpoint")
    width, _two_state, reason = type_width_2s(expression.type)
    if width != 32 or reason is not None:
        return unsupported(sm, expression, "CallExpression:associative-empty-endpoint-type")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": width, "bits": "0" * width,
        "associative_empty_endpoint": expression.subroutineName,
    }, expression.type)


def _dynamic_array_literal_size_method(expression):
    """Recognize ``size()`` after one sampled literal dynamic-array resize.

    The flat store already expands a constant ``new[N]`` allocation into
    independent cells.  Its length is therefore an exact scalar fact, while
    later resizes, dynamic receivers, and other array methods remain loud.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or expression.subroutineName != "size"
                or len(expression.arguments) != 1):
            return False
        receiver = expression.arguments[0]
        if (type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)):
            return False
        canonical = getattr(getattr(receiver, "type", None), "canonicalType", None)
        if type(canonical).__name__ != "DynamicArrayType":
            return False
        symbol = getattr(receiver, "symbol", None)
        if symbol is None:
            return False
        count = _dynamic_array_constant_extent(symbol)
        if count is None:
            return False
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        name = re.escape(getattr(symbol, "name", ""))
        if not name or not source:
            return False
        # Keep the receiver source-pure: the one allocation and size queries
        # are the only whole-array uses allowed by this object-free lowering.
        methods = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + name
            + r"\s*\.\s*([A-Za-z_$][A-Za-z0-9_$]*)"
            + r"(?:\s*\(\s*\))?", source))
        if not methods or any(m.group(1) != "size" for m in methods):
            return False
        return True
    except Exception:
        return False


def _convert_dynamic_array_literal_size(sm, expression):
    if not _dynamic_array_literal_size_method(expression):
        return unsupported(sm, expression, "CallExpression:dynamic-array-size")
    receiver = expression.arguments[0]
    count = _dynamic_array_constant_extent(receiver.symbol)
    width = getattr(expression.type, "bitWidth", None)
    if count is None or width is None or width <= 0:
        return unsupported(sm, expression, "CallExpression:dynamic-array-size")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": width,
        "bits": format(count & ((1 << width) - 1), f"0{width}b"),
        "dynamic_array_literal_size": True,
    }, expression.type)


def _semaphore_zero_method(expression):
    """Recognize state-free semaphore ``get(0)``/``put(0)``/``try_get(0)``.

    IEEE 1800-2023 §15.3.2–15.3.4 specifies that a zero key count neither
    consumes nor returns keys, ``get(0)`` cannot block, and ``try_get(0)``
    succeeds. The self-check state does not represent semaphore handles, so
    this narrow rule only erases a call whose receiver has a preceding
    ``= new(...)`` in the same source and whose sole argument is the literal
    integral zero. Any dynamic count, unproven/null receiver, or other method
    remains loud.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or expression.isSystemCall
                or expression.subroutineName not in ("get", "put", "try_get")
                or len(expression.arguments) != 1
                or _literal_integral_value(expression.arguments[0]) != 0):
            return False
        receiver = getattr(expression, "thisClass", None)
        if (receiver is None or type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)):
            return False
        receiver_type = getattr(receiver, "type", None)
        canonical = getattr(receiver_type, "canonicalType", None)
        if (type(canonical).__name__ != "ClassType"
                or getattr(canonical, "name", None) != "semaphore"):
            return False
        name = getattr(getattr(receiver, "symbol", None), "name", "")
        if not name:
            return False
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        # A source-level constructor assignment is the conservative nullness
        # witness for this erased handle.  Without it a null method call would
        # raise at run time, so type information alone is insufficient.
        return re.search(r"(?<![A-Za-z0-9_$])" + re.escape(name)
                         + r"\s*=\s*new\s*\(", source) is not None
    except Exception:
        return False


def _convert_semaphore_zero_try_get(sm, expression):
    """Return the successful scalar result of ``semaphore.try_get(0)``."""
    if not _semaphore_zero_method(expression) or expression.subroutineName != "try_get":
        return unsupported(sm, expression, "CallExpression:semaphore-try-get")
    width = getattr(expression.type, "bitWidth", None)
    if width is None or width <= 0:
        return unsupported(sm, expression, "CallExpression:semaphore-try-get-width")
    return signed_metadata({
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": width,
        "bits": ("0" * (width - 1)) + "1",
        "semaphore_zero_try_get": True,
    }, expression.type)


def _semaphore_zero_try_get(expression):
    return (_semaphore_zero_method(expression)
            and expression.subroutineName == "try_get")


def _semaphore_literal_try_get_state(expression):
    """Return the source-ordered state of a literal semaphore method.

    This is intentionally a small, object-free slice of IEEE 1800-2023
    §15.3.2–15.3.4. A handle must have exactly one direct ``new(N)``
    constructor, every use of it must be a literal ``put``, ``get``, or
    ``try_get`` (the frontend supplies the default argument as literal one),
    and no other named use or alias may occur. The returned ``available``
    count is the value immediately before this call; ``request`` is the
    literal key count and ``success`` records whether the call can complete
    without blocking.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or expression.isSystemCall
                or expression.subroutineName not in ("put", "get", "try_get")):
            return None
        receiver = getattr(expression, "thisClass", None)
        if (type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)):
            return None
        symbol = getattr(receiver, "symbol", None)
        canonical = getattr(getattr(receiver, "type", None), "canonicalType", None)
        if (symbol is None or type(canonical).__name__ != "ClassType"
                or getattr(canonical, "name", None) != "semaphore"):
            return None
        arguments = list(getattr(expression, "arguments", []))
        if len(arguments) != 1:
            return None
        request = _literal_integral_value(arguments[0])
        negative_request = request is not None and request < 0
        # The pinned conformance witness records this simulator's §15.3.4
        # behavior: a negative literal keyCount on ``try_get`` is treated as
        # one.  Keep the compatibility rule specific to that nonblocking
        # method; negative ``put``/``get`` calls remain outside the snapshot.
        if request is None or (negative_request
                               and expression.subroutineName != "try_get"):
            return None
        if negative_request:
            request = 1

        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        code_source = _sv_code_source(source)
        if not source or not getattr(symbol, "name", ""):
            return None
        name = re.escape(symbol.name)
        current_start = getattr(getattr(getattr(expression, "sourceRange", None),
                                        "start", None), "offset", None)
        if current_start is None:
            return None
        # Prove the source-text constructor with the bound frontend tree
        # first.  The text scan below supplies the compact source ordering,
        # while this AST check prevents a comment or string mentioning
        # ``sem = new(N)`` from becoming an object witness.
        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        if instance is None:
            return None
        constructor_nodes = []

        def find_constructor(node):
            if type(node).__name__ == "AssignmentExpression":
                left = getattr(node, "left", None)
                if (getattr(left, "symbol", None) is symbol
                        and type(left).__name__ == "NamedValueExpression"
                        and getattr(node, "op", None) is None
                        and getattr(node, "timingControl", None) is None
                        and not getattr(node, "isNonBlocking", False)
                        and _semaphore_new_nonnegative_literal(getattr(node, "right", None))):
                    constructor_nodes.append(node)

        instance.visit(find_constructor)
        initializer = getattr(symbol, "initializer", None)
        if _semaphore_new_nonnegative_literal(initializer):
            constructor_nodes.append(initializer)
        if len(constructor_nodes) != 1:
            return None

        constructor_re = re.compile(
            r"(?<![A-Za-z0-9_$])" + name
            + r"\s*=\s*new\s*\(\s*([+-]?\d+)?\s*\)")
        constructors = list(constructor_re.finditer(code_source))
        if len(constructors) != 1:
            return None
        constructor = constructors[0]
        initial = int(constructor.group(1), 10) if constructor.group(1) else 0
        if initial < 0 or constructor.start() >= current_start:
            return None
        constructor_value = constructor_nodes[0]
        if type(constructor_value).__name__ == "AssignmentExpression":
            constructor_value = getattr(constructor_value, "right", None)
        call = getattr(constructor_value, "constructorCall", None)
        constructor_args = list(getattr(call, "arguments", []))
        proven_initial = (_literal_integral_value(constructor_args[0])
                          if len(constructor_args) == 1 else
                          0 if not constructor_args else None)
        if proven_initial != initial:
            return None
        method_re = re.compile(
            r"(?<![A-Za-z0-9_$])" + name
            + r"\s*\.\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\(")
        methods = list(method_re.finditer(code_source))
        if not methods:
            return None
        values_by_start = {}
        for method in methods:
            if method.start() <= constructor.end():
                continue
            if method.group(1) not in ("put", "get", "try_get"):
                return None
        # Any post-construction bare occurrence must be one of the admitted
        # method receivers. This rejects aliases and ordinary reads.
        for occurrence in re.finditer(r"(?<![A-Za-z0-9_$])" + name
                                      + r"(?![A-Za-z0-9_$])", code_source):
            if occurrence.start() <= constructor.end():
                continue
            if not any(method.start() == occurrence.start() for method in methods):
                return None
        current_methods = [method for method in methods
                           if method.start() == current_start]
        if not current_methods:
            # pyslang's source range begins at the call, while the regex begins
            # at the receiver. Some elaborated calls instead begin at the
            # first argument, so accept the nearest preceding receiver.
            current_methods = [method for method in methods
                               if method.start() <= current_start <= method.end()]
        if not current_methods:
            preceding = [method for method in methods
                         if method.start() <= current_start]
            if preceding:
                current_methods = [max(preceding, key=lambda item: item.start())]
        if len(current_methods) != 1:
            return None
        current_method_start = current_methods[0].start()
        prior = [method for method in methods
                 if constructor.end() < method.start() < current_method_start]
        for method in methods:
            text = code_source[method.end():]
            close = text.find(")")
            if close < 0:
                return None
            arg_text = text[:close].strip()
            if not arg_text:
                value = 1
            elif re.fullmatch(r"[+-]?\d+", arg_text):
                value = int(arg_text, 10)
            else:
                return None
            if value < 0:
                if method.group(1) != "try_get":
                    return None
                value = 1
            values_by_start[method.start()] = value
        available = initial
        for method in sorted(prior, key=lambda item: item.start()):
            value = values_by_start[method.start()]
            method_name = method.group(1)
            if method_name == "put":
                available += value
            elif method_name == "get":
                if value > available:
                    return None
                available -= value
            elif value <= available:
                available -= value
        method_name = current_methods[0].group(1)
        success = method_name == "put" or request <= available
        return {"available": available, "request": request,
                "success": success, "method": method_name,
                "negative_key_normalized": negative_request}
    except Exception:
        return None


def _semaphore_literal_try_get(expression):
    state = _semaphore_literal_try_get_state(expression)
    return state is not None and state.get("method") == "try_get"


def _semaphore_literal_put_get(expression):
    """Recognize a literal ``put``/nonblocking ``get`` statement.

    A direct source-ordered balance proves that ``get`` has enough keys and
    therefore cannot enter the scheduler. The statement result is discarded,
    so the self-check representation may erase both methods while retaining
    the exact balance for later ``try_get`` expressions.
    """
    state = _semaphore_literal_try_get_state(expression)
    return (state is not None
            and state.get("method") in ("put", "get")
            and state.get("success", False))


def _convert_semaphore_literal_try_get(sm, expression):
    state = _semaphore_literal_try_get_state(expression)
    if state is None:
        return unsupported(sm, expression, "CallExpression:semaphore-try-get")
    width = getattr(expression.type, "bitWidth", None)
    if width is None or width <= 0:
        return unsupported(sm, expression, "CallExpression:semaphore-try-get-width")
    result = 1 if state["success"] else 0
    return signed_metadata({
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": width,
        "bits": ("0" * (width - 1)) + str(result),
        "semaphore_literal_try_get": True,
        "semaphore_available": state["available"],
        "semaphore_request": state["request"],
        "semaphore_negative_key_normalized": state.get(
            "negative_key_normalized", False),
    }, expression.type)


def _mailbox_empty_num_method(expression):
    """Recognize ``num()`` on a newly constructed, otherwise untouched mailbox."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or expression.isSystemCall
                or expression.subroutineName != "num"
                or len(expression.arguments) != 0):
            return False
        receiver = getattr(expression, "thisClass", None)
        if (receiver is None or type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)):
            return False
        canonical = getattr(getattr(receiver, "type", None), "canonicalType", None)
        if (type(canonical).__name__ != "ClassType"
                or getattr(canonical, "name", None) != "mailbox"):
            return False
        name = getattr(getattr(receiver, "symbol", None), "name", "")
        if not name:
            return False
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        constructor = re.search(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"\s*=\s*new\s*\(\s*\)", source)
        if constructor is None:
            return False
        if re.search(r"(?<![A-Za-z0-9_$])" + re.escape(name)
                     + r"\s*\.", source[:constructor.start()]):
            return False
        occurrences = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", source))
        return all(source[m.end():].lstrip().startswith(".num")
                   for m in occurrences if m.start() > constructor.end())
    except Exception:
        return False


def _mailbox_empty_try_method(expression):
    """Recognize ``try_get``/``try_peek`` on an untouched ``mailbox new()``."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or expression.isSystemCall
                or expression.subroutineName not in ("try_get", "try_peek")
                or len(expression.arguments) != 1):
            return False
        receiver = getattr(expression, "thisClass", None)
        if (type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)):
            return False
        canonical = getattr(getattr(receiver, "type", None), "canonicalType", None)
        if (type(canonical).__name__ != "ClassType"
                or getattr(canonical, "name", None) != "mailbox"):
            return False
        name = getattr(getattr(receiver, "symbol", None), "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if not name or not source:
            return False
        constructor = re.search(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"\s*=\s*new\s*\(\s*\)", source)
        if constructor is None:
            return False
        position = getattr(getattr(expression, "sourceRange", None), "start", None)
        position = getattr(position, "offset", None)
        if position is None or position < constructor.end():
            return False
        methods = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"\s*\.\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\(", source))
        if not methods:
            return False
        return all(method.group(1) in ("try_get", "try_peek")
                   for method in methods if method.start() >= constructor.end())
    except Exception:
        return False


def _convert_mailbox_empty_try_method(sm, expression):
    if not _mailbox_empty_try_method(expression):
        return unsupported(sm, expression, "CallExpression:mailbox-try")
    width = getattr(expression.type, "bitWidth", None)
    if width is None or width <= 0:
        return unsupported(sm, expression, "CallExpression:mailbox-try-width")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": width, "bits": "0" * width,
        "mailbox_empty_try": expression.subroutineName,
    }, expression.type)


def _mailbox_type_mismatch_try_get(expression):
    """Recognize the negative result of an untyped mailbox type mismatch.

    IEEE 1800-2023 §15.4.6 specifies a negative return when the destination
    type is not equivalent to the queued message type.  This narrow lowering
    models the source-pure ``new(); put(literal); try_get(named)`` shape.  It
    does not publish a destination value and therefore leaves the flat state
    unchanged; all other mailbox activity remains on the FIFO boundary.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or expression.isSystemCall
                or expression.subroutineName != "try_get"
                or len(expression.arguments) != 1):
            return False
        receiver = getattr(expression, "thisClass", None)
        if (type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)):
            return False
        canonical = getattr(getattr(receiver, "type", None), "canonicalType", None)
        if (type(canonical).__name__ != "ClassType"
                or getattr(canonical, "name", None) != "mailbox"
                or getattr(canonical, "arrayElementType", None) is not None):
            return False
        target = expression.arguments[0]
        if (type(target).__name__ != "NamedValueExpression"
                or getattr(target, "bad", False)):
            return False
        width, _two_state, reason = type_width_2s(expression.type)
        if (width != 32 or reason is not None
                or not getattr(expression.type, "isIntegral", False)
                or not getattr(expression.type, "isSigned", False)):
            return False
        name = getattr(getattr(receiver, "symbol", None), "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if not name or not source:
            return False
        code_source = _sv_code_source(source)
        constructor = re.search(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"\s*=\s*new\s*\(\s*\)", code_source)
        if constructor is None:
            return False
        position = getattr(getattr(getattr(expression, "sourceRange", None),
                                  "start", None), "offset", None)
        if position is None or position < constructor.end():
            return False
        # The frontend's call graph gives the exact message and target types;
        # require one literal put before this call and no other method shape.
        instance = getattr(getattr(getattr(receiver, "symbol", None),
                                   "parentScope", None),
                           "containingInstance", None)
        if instance is None:
            return False
        calls = []
        def inspect(node):
            if type(node).__name__ != "CallExpression":
                return
            call_receiver = getattr(node, "thisClass", None)
            if (type(call_receiver).__name__ == "NamedValueExpression"
                    and getattr(call_receiver, "symbol", None)
                    is getattr(receiver, "symbol", None)):
                offset = getattr(getattr(getattr(node, "sourceRange", None),
                                         "start", None), "offset", None)
                if offset is not None and offset >= constructor.end():
                    calls.append((offset, node))
        instance.visit(inspect)
        calls.sort(key=lambda item: item[0])
        if len(calls) != 2 or calls[-1][1] is not expression:
            return False
        put = calls[0][1]
        if (put.subroutineName != "put" or len(put.arguments) != 1
                or not _integral_literal_source(put.arguments[0])
                or not _case_source_expression_ok(put.arguments[0])):
            return False
        message = put.arguments[0]
        return not message.type.isEquivalent(target.type)
    except Exception:
        return False


def _convert_mailbox_type_mismatch_try_get(sm, expression):
    if not _mailbox_type_mismatch_try_get(expression):
        return None
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": 32, "bits": "1" * 32,
        "mailbox_type_mismatch_try_get": True,
    }, expression.type)


def _event_triggered_false(expression):
    """Recognize ``event.triggered()`` before any trigger in this flat tier."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "triggered"
                or len(expression.arguments) != 1):
            return False
        receiver = expression.arguments[0]
        if type(receiver).__name__ != "NamedValueExpression":
            return False
        if type(getattr(receiver.type, "canonicalType", None)).__name__ != "EventType":
            return False
        symbol = getattr(receiver, "symbol", None)
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if symbol is None or not name or not source:
            return False
        occurrences = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", source))
        if not occurrences:
            return False
        for occurrence in occurrences[1:]:
            tail = source[occurrence.end():].lstrip()
            if tail.startswith(".triggered") or re.match(r"=\s*null\b", tail):
                continue
            return False
        return True
    except Exception:
        return False


def _convert_event_triggered_false(sm, expression):
    if not _event_triggered_false(expression):
        return unsupported(sm, expression, "CallExpression:event-triggered")
    width = getattr(expression.type, "bitWidth", None)
    if width != 1:
        return unsupported(sm, expression, "CallExpression:event-triggered-width")
    return {"kind": "Literal", "span": node_span(sm, expression),
            "width": 1, "bits": "0", "event_triggered_false": True}


def _mailbox_literal_sequence(expression):
    """Recognize a direct unbounded mailbox ``put``/``num`` sequence.

    The self-check store has no mailbox object.  An unbounded mailbox made by
    literal ``new()`` nevertheless has an exact scalar count when every use is
    a source-pure ``put`` or a ``num`` query on that same handle.  Keep the
    source scan conservative: aliases, assignments, other methods, bounded
    constructors, and calls before construction all remain loud.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or expression.isSystemCall
                or expression.subroutineName not in ("put", "num")):
            return None
        receiver = getattr(expression, "thisClass", None)
        if (receiver is None or type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)):
            return None
        canonical = getattr(getattr(receiver, "type", None), "canonicalType", None)
        if (type(canonical).__name__ != "ClassType"
                or getattr(canonical, "name", None) != "mailbox"):
            return None
        name = getattr(getattr(receiver, "symbol", None), "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if not name or not source:
            return None
        constructor = re.search(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"\s*=\s*new\s*\(\s*\)", source)
        if constructor is None:
            return None
        position = getattr(getattr(expression, "sourceRange", None), "start", None)
        position = getattr(position, "offset", None)
        if position is None or position < constructor.end():
            return None
        methods = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"\s*\.\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\(", source))
        if not methods:
            return None
        # Every post-construction use must be one of the two scalar methods;
        # this also rejects aliases and later writes by requiring all bare
        # occurrences to be constructor or method receivers.
        bare = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", source))
        for match in bare:
            if match.start() < constructor.start():
                continue
            tail = source[match.end():].lstrip()
            if match.start() == constructor.start():
                continue
            if not tail.startswith("."):
                return None
        for method in methods:
            if method.start() < constructor.end():
                continue
            if method.group(1) not in ("put", "num"):
                return None
        current = [m for m in methods if m.start() <= position]
        current_match = [m for m in current if m.start() ==
                         getattr(getattr(expression, "sourceRange", None), "start", None).offset]
        if not current_match:
            return None
        if expression.subroutineName == "put":
            if len(expression.arguments) != 1 or not _case_source_expression_ok(expression.arguments[0]):
                return None
        else:
            if expression.arguments:
                return None
        count = sum(1 for method in current if method.group(1) == "put")
        return count
    except Exception:
        return None


def _mailbox_literal_get_state(sm, expression):
    """Sample a scalar FIFO mailbox sequence through direct method calls.

    An unbounded mailbox has no flat representation in the self-check state,
    but a linear sequence of literal integral ``put``/``try_put`` calls and
    scalar output ``get``/``try_get`` calls is an exact queue snapshot.  Keep
    the scan source-ordered and reject aliases, bounded constructors, dynamic
    messages, empty gets, and every method outside the admitted FIFO surface.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or expression.isSystemCall
                or expression.subroutineName not in (
                    "put", "get", "num", "try_put", "try_get")):
            return None
        receiver = getattr(expression, "thisClass", None)
        if (receiver is None or type(receiver).__name__ != "NamedValueExpression"
                or getattr(receiver, "bad", False)):
            return None
        canonical = getattr(getattr(receiver, "type", None), "canonicalType", None)
        if (type(canonical).__name__ != "ClassType"
                or getattr(canonical, "name", None) != "mailbox"):
            return None
        symbol = getattr(receiver, "symbol", None)
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if symbol is None or not name or not source:
            return None
        constructor = re.search(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"\s*=\s*new\s*\(\s*\)", source)
        if constructor is None:
            return None
        position = getattr(getattr(expression, "sourceRange", None),
                           "start", None)
        position = getattr(position, "offset", None)
        if position is None or position < constructor.end():
            return None

        # Every post-construction bare occurrence must be a method receiver.
        # This rejects handles passed through another variable or subroutine
        # without depending on frontend source-range details.
        for occurrence in re.finditer(
                r"(?<![A-Za-z0-9_$])" + re.escape(name)
                + r"(?![A-Za-z0-9_$])", source):
            if occurrence.start() <= constructor.end():
                continue
            if not source[occurrence.end():].lstrip().startswith("."):
                return None

        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        if instance is None:
            return None
        calls = []
        scalar_writes = []
        control_ranges = []

        def inspect(node):
            kind = type(node).__name__
            if any(token in kind for token in (
                    "Conditional", "Case", "For", "While", "Repeat",
                    "Foreach", "Forever", "Wait", "Fork")):
                start = getattr(getattr(getattr(node, "sourceRange", None),
                                        "start", None), "offset", None)
                end = getattr(getattr(getattr(node, "sourceRange", None),
                                      "end", None), "offset", None)
                if start is not None and end is not None:
                    control_ranges.append((start, end))
            if type(node).__name__ != "CallExpression":
                if type(node).__name__ == "VariableDeclStatement":
                    declared = getattr(node, "symbol", None)
                    initializer = getattr(declared, "initializer", None)
                    if declared is not None and initializer is not None:
                        offset = getattr(getattr(getattr(initializer,
                                                    "sourceRange", None),
                                                "start", None),
                                         "offset", None)
                        value = None
                        if (_integral_literal_source(initializer)
                                and _case_source_expression_ok(initializer)):
                            value = convert_expr(sm, initializer)
                            if (value is None or value.get("kind") == "Unsupported"
                                    or not _case_expression_ok(value)):
                                value = None
                        if offset is not None:
                            scalar_writes.append((offset, declared, value))
                elif type(node).__name__ == "AssignmentExpression":
                    left = getattr(node, "left", None)
                    declared = getattr(left, "symbol", None)
                    offset = getattr(getattr(getattr(node, "sourceRange", None),
                                             "start", None), "offset", None)
                    value = None
                    right = getattr(node, "right", None)
                    if (declared is not None and offset is not None
                            and not getattr(node, "isNonBlocking", False)
                            and _integral_literal_source(right)
                            and _case_source_expression_ok(right)):
                        value = convert_expr(sm, right)
                        if (value is None or value.get("kind") == "Unsupported"
                                or not _case_expression_ok(value)):
                            value = None
                    if declared is not None and offset is not None:
                        scalar_writes.append((offset, declared, value))
                return
            receiver_node = getattr(node, "thisClass", None)
            if (type(receiver_node).__name__ == "NamedValueExpression"
                    and getattr(receiver_node, "symbol", None) is symbol):
                offset = getattr(getattr(getattr(node, "sourceRange", None),
                                         "start", None), "offset", None)
                if offset is not None and offset >= constructor.end():
                    calls.append((offset, node))

        instance.visit(inspect)
        calls.sort(key=lambda item: item[0])
        control_ranges = list(set(control_ranges))
        # A count query is a pure read and may occur in a condition or a
        # diagnostic argument.  Mutating calls still have to be linear: a
        # branch-local put/get/try_* would make the replay path-dependent.
        if any(getattr(node, "subroutineName", "") != "num"
               and start < offset < end
               for offset, node in calls
               for start, end in control_ranges):
            return None
        scalar_writes.sort(key=lambda item: item[0])
        if any(any(start < write_offset < end
                   for write_offset, _symbol, _value in scalar_writes)
               for start, end in control_ranges):
            return None
        if not any(node is expression for _, node in calls):
            return None
        if any(getattr(node, "subroutineName", "") not in (
                    "put", "get", "num", "try_put", "try_get")
               for _, node in calls):
            return None

        def formal_message_width(call):
            """Return a typed mailbox method's scalar message width.

            Built-in untyped mailboxes expose an ``untyped`` formal and keep
            the old width-from-message behavior.  Parameterized integral
            mailboxes expose a concrete formal; requiring the source argument
            and output target to match it keeps truncating or widening calls
            loud instead of silently changing the queued value.
            """
            try:
                formal = list(getattr(call.subroutine, "arguments", []))
                if len(formal) != 1:
                    return None
                width, _two_state, reason = type_width_2s(formal[0].type)
                return width if width is not None and reason is None else None
            except Exception:
                return None

        def source_integral_width(node):
            """Width before pyslang inserts a formal-argument conversion."""
            raw = node
            while type(raw).__name__ == "ConversionExpression":
                raw = getattr(raw, "operand", None)
                if raw is None:
                    return None
            try:
                width, _two_state, reason = type_width_2s(raw.type)
                return width if width is not None and reason is None else None
            except Exception:
                return None

        def literal_message(node, offset, call):
            if not _case_source_expression_ok(node):
                return None
            named = []

            def inspect_value(value):
                if type(value).__name__ in ("NamedValueExpression",
                                            "HierarchicalValueExpression"):
                    named.append(value)

            _visit_selected_expression(node, inspect_value)
            width, _two_state, reason = type_width_2s(node.type)
            if width is None or reason is not None:
                return None
            expected_width = formal_message_width(call)
            source_width = source_integral_width(node)
            if (expected_width is not None
                    and (source_width is not None and source_width != expected_width
                         or source_width is None and width != expected_width)):
                return None
            if named:
                # The variable-message extension is deliberately one direct
                # scalar name.  Replay its latest pure-literal write from the
                # linear source order; aliases, aggregates and expressions
                # combining names remain outside the snapshot.
                if (len(named) != 1
                        or type(node).__name__ != "NamedValueExpression"
                        or type(named[0]).__name__ != "NamedValueExpression"):
                    return None
                target = getattr(named[0], "symbol", None)
                writes = [value for write_offset, symbol_value, value
                          in scalar_writes
                          if symbol_value is target and write_offset < offset]
                if not writes or writes[-1] is None:
                    return None
                value = writes[-1]
            else:
                value = convert_expr(sm, node)
            if (value is None or value.get("kind") == "Unsupported"
                    or width_of(value) != width or not _case_expression_ok(value)):
                return None
            return value, width

        queue = []
        prior_activity = False
        current_result = None
        for _, node in calls:
            method = str(getattr(node, "subroutineName", ""))
            arguments = list(getattr(node, "arguments", []))
            if node is expression:
                current_result = (method, queue[:], prior_activity)
                break
            if method in ("put", "try_put"):
                if len(arguments) != 1:
                    return None
                message = literal_message(arguments[0], _, node)
                if message is None:
                    return None
                queue.append(message)
                prior_activity = True
            elif method in ("get", "try_get"):
                if len(arguments) != 1 or not queue:
                    if method == "try_get" and len(arguments) == 1:
                        target, admitted = legacy_blocking_target(
                            sm, arguments[0], True)
                        if (not admitted or target.get("kind") != "Ident"
                                or (formal_message_width(node) is not None
                                    and (source_integral_width(arguments[0])
                                         is not None
                                         and source_integral_width(arguments[0])
                                         != formal_message_width(node))
                                    or (formal_message_width(node) is not None
                                        and source_integral_width(arguments[0])
                                        is None
                                        and width_of(target)
                                        != formal_message_width(node)))):
                            return None
                        prior_activity = True
                        continue
                    return None
                target, admitted = legacy_blocking_target(sm, arguments[0], True)
                if not admitted or target.get("kind") != "Ident":
                    return None
                target_width = width_of(target)
                expected_width = formal_message_width(node)
                source_target_width = source_integral_width(arguments[0])
                if ((expected_width is not None
                     and ((source_target_width is not None
                           and source_target_width != expected_width)
                          or (source_target_width is None
                              and target_width != expected_width)))
                        or target_width != queue[0][1]):
                    return None
                queue.pop(0)
                prior_activity = True
            elif method == "num":
                if arguments:
                    return None
        if current_result is None:
            return None
        method, available, activity = current_result
        if method == "put":
            if len(expression.arguments) != 1:
                return None
            message = literal_message(expression.arguments[0], position, expression)
            if message is None:
                return None
            return {"method": method, "value": message[0],
                    "width": message[1], "count": len(available),
                    "activity": activity}
        if method == "try_put":
            if len(expression.arguments) != 1:
                return None
            message = literal_message(expression.arguments[0], position, expression)
            if message is None:
                return None
            return {"method": method, "value": message[0],
                    "width": message[1], "count": len(available),
                    "activity": activity, "success": True}
        if method == "num":
            if expression.arguments:
                return None
            return {"method": method, "count": len(available),
                    "activity": activity}
        if len(expression.arguments) != 1:
            return None
        target, admitted = legacy_blocking_target(sm, expression.arguments[0], True)
        if not admitted or target.get("kind") != "Ident":
            return None
        target_width = width_of(target)
        expected_width = formal_message_width(expression)
        source_target_width = source_integral_width(expression.arguments[0])
        if (expected_width is not None
                and ((source_target_width is not None
                      and source_target_width != expected_width)
                     or (source_target_width is None
                         and target_width != expected_width))):
            return None
        if method == "try_get" and not available:
            return {"method": method, "target": target, "count": 0,
                    "activity": activity, "success": False}
        if not available:
            return None
        value, value_width = available[0]
        if target_width != value_width:
            return None
        return {"method": method, "target": target, "value": value,
                "width": value_width, "count": len(available),
                "activity": activity, "success": method == "try_get"}
    except Exception:
        return None


def _convert_mailbox_empty_num(sm, expression):
    if not _mailbox_empty_num_method(expression):
        return unsupported(sm, expression, "CallExpression:mailbox-num")
    width = getattr(expression.type, "bitWidth", None)
    if width is None or width <= 0:
        return unsupported(sm, expression, "CallExpression:mailbox-num-width")
    return signed_metadata({
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": width,
        "bits": "0" * width,
        "mailbox_empty_num": True,
    }, expression.type)


def _convert_mailbox_literal_num(sm, expression):
    count = _mailbox_literal_sequence(expression)
    if count is None or expression.subroutineName != "num":
        return unsupported(sm, expression, "CallExpression:mailbox-num")
    width = getattr(expression.type, "bitWidth", None)
    if width is None or width <= 0:
        return unsupported(sm, expression, "CallExpression:mailbox-num-width")
    return signed_metadata({
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": width,
        "bits": format(count & ((1 << width) - 1), f"0{width}b"),
        "mailbox_literal_num": True,
    }, expression.type)


def _convert_mailbox_literal_state_call(sm, expression):
    """Render a literal mailbox FIFO method after source-ordered activity."""
    state = _mailbox_literal_get_state(sm, expression)
    if state is None:
        return None
    method = expression.subroutineName
    if method in ("try_put", "try_get"):
        width = getattr(expression.type, "bitWidth", None)
        if width is None or width <= 0:
            return unsupported(sm, expression, "CallExpression:mailbox-try-width")
        result = 1 if state.get("success", False) else 0
        converted = signed_metadata({
            "kind": "Literal", "span": node_span(sm, expression),
            "width": width,
            "bits": ("0" * (width - 1)) + str(result),
            "mailbox_literal_try": method,
            "mailbox_try_success": bool(state.get("success", False)),
        }, expression.type)
        # ``try_get`` is a function with an output argument.  Expression
        # lowering carries the direct scalar store as metadata; assignment
        # conversion turns it into a preceding BlockingAssign so the output
        # update is not lost when the return value is assigned elsewhere.
        if method == "try_get" and state.get("success", False):
            converted["mailbox_literal_try_get_target"] = state["target"]
            converted["mailbox_literal_try_get_value"] = state["value"]
        return converted
    # ``num()`` is also meaningful immediately after construction: the
    # mailbox contains zero messages before the first put/get.  The state
    # scanner already proves the direct constructor, source order, and all
    # subsequent methods, so an inactive snapshot is exact rather than an
    # opaque handle guess.
    if method != "num":
        return None
    # Keep the dedicated untouched-mailbox marker for the old one-query
    # shape; it is useful to clients that distinguish an empty object from a
    # stateful FIFO snapshot.  Once another operation appears in the proven
    # source sequence, this path owns the zero-count query as well.
    if (not state.get("activity", False)
            and _mailbox_empty_num_method(expression)):
        return None
    width = getattr(expression.type, "bitWidth", None)
    if width is None or width <= 0 or state["count"] < 0:
        return unsupported(sm, expression, "CallExpression:mailbox-num")
    bits = format(state["count"] & ((1 << width) - 1), f"0{width}b")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": width, "bits": bits,
        "mailbox_literal_num": True,
    }, expression.type)


def _queue_history_literal(expression, instance, before):
    """Resolve one named integral input from one prior literal write."""
    value = _literal_integral_value(expression)
    if value is not None:
        return value
    if type(expression).__name__ != "NamedValueExpression":
        return None
    symbol = getattr(expression, "symbol", None)
    if symbol is None or getattr(symbol, "initializer", None) is not None:
        return None
    assignments = []
    invalid = False

    def inspect(node):
        nonlocal invalid
        if type(node).__name__ != "AssignmentExpression":
            return
        if getattr(getattr(node, "left", None), "symbol", None) is not symbol:
            return
        if (getattr(node, "op", None) is not None
                or getattr(node, "timingControl", None) is not None
                or getattr(node, "isNonBlocking", False)):
            invalid = True
            return
        assigned = _literal_integral_value(getattr(node, "right", None))
        if assigned is None:
            invalid = True
            return
        start = getattr(getattr(getattr(node, "sourceRange", None),
                                "start", None), "offset", -1)
        assignments.append((start, assigned))

    instance.visit(inspect)
    prior = [value for position, value in assignments if position < before]
    if invalid or len(assignments) != 1 or len(prior) != 1:
        return None
    return prior[0]


def _q_add_output_shape(expression):
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$q_add"
                or len(expression.arguments) != 4):
            return False
        status = expression.arguments[3]
        return (type(status).__name__ == "AssignmentExpression"
                and status.op is None
                and status.timingControl is None
                and type(status.right).__name__ == "EmptyArgumentExpression")
    except Exception:
        return False


def _q_add_source_shape(expression, instance=None):
    """Whether a queue add has only literal inputs and one output status.

    The self-check state has no queue payload object.  Keep this recognizer
    deliberately source-pure: queue ID, job, and inform are direct integral
    literals, while the final argument is the ordinary output-assignment
    spelling used by the system task.
    """
    try:
        if not _q_add_output_shape(expression):
            return False
        qid, job, inform, status = expression.arguments
        if instance is None:
            return all(_literal_integral_value(argument) is not None
                       for argument in (qid, job, inform))
        before = getattr(getattr(getattr(expression, "sourceRange", None),
                                 "start", None), "offset", -1)
        return all(_queue_history_literal(argument, instance, before) is not None
                   for argument in (qid, job, inform))
    except Exception:
        return False


def _q_full_source_shape(expression):
    """Whether a queue-full query has a literal ID and output status."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$q_full"
                or len(expression.arguments) != 2):
            return False
        qid, status = expression.arguments
        return (_literal_integral_value(qid) is not None
                and type(status).__name__ == "AssignmentExpression"
                and status.op is None
                and status.timingControl is None
                and type(status.right).__name__ == "EmptyArgumentExpression")
    except Exception:
        return False


def _q_exam_output_shape(expression):
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$q_exam"
                or len(expression.arguments) != 4):
            return False
        _qid, stat_code, stat_value, status = expression.arguments
        # IEEE 1800-2023 §20.15.5 Table 20-10 assigns codes 1--6 to
        # current/max length and timing statistics.  The flat self-check
        # state can replay the length columns exactly; the timing columns
        # are admitted only for a zero-time history below.
        if (_literal_integral_value(stat_code) not in (1, 2, 3, 4, 5, 6)):
            return False
        return all(type(output).__name__ == "AssignmentExpression"
                   and output.op is None
                   and output.timingControl is None
                   and type(output.right).__name__ == "EmptyArgumentExpression"
                   for output in (stat_value, status))
    except Exception:
        return False


def _q_exam_source_shape(expression, instance=None):
    """Whether a queue exam asks for a literal or prior-written ID."""
    try:
        if not _q_exam_output_shape(expression):
            return False
        qid = expression.arguments[0]
        if instance is None:
            return _literal_integral_value(qid) is not None
        before = getattr(getattr(getattr(expression, "sourceRange", None),
                                 "start", None), "offset", -1)
        return _queue_history_literal(qid, instance, before) is not None
    except Exception:
        return False


def _q_initialize_status_call(sm, expression):
    """Lower a state-free ``$q_initialize`` status result.

    The queue model is outside the flat self-check state, but IEEE 1800-2023
    §20.15.6 defines the scalar status for a few argument errors.  A sole
    queue task with a literal type/capacity can therefore publish that status
    directly to its output lvalue.  A second source-ordered initialization of
    the same literal queue ID is also admitted: the first valid creation
    reports 0 and the duplicate reports 6, without exposing the queue object.
    A source-ordered sequence of literal ``$q_add`` calls is also admitted;
    those calls retain only their scalar status and are handled by
    ``_q_add_status_call``.  Any other queue operation remains on the ordinary
    loud boundary.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$q_initialize"
                or len(expression.arguments) != 4):
            return None
        qid, qtype, max_length, output = expression.arguments
        if (type(output).__name__ != "AssignmentExpression"
                or output.op is not None
                or output.timingControl is not None
                or type(output.right).__name__ != "EmptyArgumentExpression"):
            return None
        if not all(_case_source_expression_ok(argument)
                   for argument in (qid, qtype, max_length)):
            return None
        qtype_value = _literal_integral_value(qtype)
        max_value = _literal_integral_value(max_length)
        if qtype_value is None or max_value is None:
            return None
        # Do not erase a status write in a file that relies on an unmodelled
        # queue object or a later operation.  Count semantic calls, not source
        # text, so comments and descriptions cannot affect the admission.
        receiver_scope = getattr(getattr(output.left, "symbol", None),
                                 "parentScope", None)
        instance = getattr(receiver_scope, "containingInstance", None)
        if instance is None:
            return None
        queue_calls = []

        def inspect(node):
            if (type(node).__name__ == "CallExpression"
                    and getattr(node, "isSystemCall", False)
                    and str(getattr(node, "subroutineName", "")).startswith("$q_")):
                queue_calls.append(node)

        instance.visit(inspect)
        queue_calls.sort(key=lambda node: getattr(
            getattr(getattr(node, "sourceRange", None), "start", None),
            "offset", -1))
        if not queue_calls or expression not in queue_calls:
            return None

        # A named queue ID is admitted only after one direct literal blocking
        # assignment before the calls.  This proves the duplicate-ID status
        # without inventing a queue store; declaration initializers, computed
        # or selected writes, and reassignment remain loud.
        def qid_value(call):
            argument = call.arguments[0]
            literal = _literal_integral_value(argument)
            if literal is not None:
                return literal
            if type(argument).__name__ != "NamedValueExpression":
                return None
            symbol = getattr(argument, "symbol", None)
            if symbol is None or getattr(symbol, "initializer", None) is not None:
                return None
            assignments = []
            invalid = False

            def inspect_assignment(node):
                nonlocal invalid
                if type(node).__name__ != "AssignmentExpression":
                    return
                left = getattr(node, "left", None)
                if getattr(left, "symbol", None) is not symbol:
                    return
                if (getattr(node, "op", None) is not None
                        or getattr(node, "timingControl", None) is not None
                        or getattr(node, "isNonBlocking", False)):
                    invalid = True
                    return
                value = _literal_integral_value(getattr(node, "right", None))
                if value is None:
                    invalid = True
                    return
                start = getattr(getattr(getattr(node, "sourceRange", None),
                                        "start", None), "offset", -1)
                assignments.append((start, value))

            instance.visit(inspect_assignment)
            if invalid or len(assignments) != 1:
                return None
            start = getattr(getattr(getattr(call, "sourceRange", None),
                                    "start", None), "offset", -1)
            prior = [value for position, value in assignments if position < start]
            return prior[0] if len(prior) == 1 else None

        qids = [qid_value(call) for call in queue_calls]
        if any(value is None for value in qids) or len(set(qids)) != 1:
            return None
        if len(queue_calls) == 2:
            first, second = queue_calls
            first_name = str(getattr(first, "subroutineName", ""))
            second_name = str(getattr(second, "subroutineName", ""))
            if first_name == "$q_initialize" and second_name == "$q_remove":
                if (_literal_integral_value(first.arguments[1]) not in (1, 2)
                        or (_literal_integral_value(first.arguments[2]) or 0) <= 0):
                    return None
            elif first_name == "$q_initialize" and second_name in (
                    "$q_add", "$q_full", "$q_exam", "$q_remove"):
                shape_ok = (_q_add_source_shape(second, instance)
                            if second_name == "$q_add"
                            else (_q_full_source_shape(second)
                                  if second_name == "$q_full"
                                  else (_q_exam_source_shape(second, instance)
                                        if second_name == "$q_exam"
                                        else _q_remove_output_shape(second))))
                if (not shape_ok
                        or _literal_integral_value(first.arguments[1]) not in (1, 2)
                        or (_literal_integral_value(first.arguments[2]) or 0) <= 0):
                    return None
            else:
                first_type = _literal_integral_value(first.arguments[1])
                first_capacity = _literal_integral_value(first.arguments[2])
                second_type = _literal_integral_value(second.arguments[1])
                second_capacity = _literal_integral_value(second.arguments[2])
                if (first_name != "$q_initialize"
                        or second_name != "$q_initialize"
                        or first_type not in (1, 2) or first_capacity is None
                        or first_capacity <= 0 or first_type != second_type
                        or first_capacity != second_capacity):
                    return None
        if len(queue_calls) > 2:
            if str(getattr(queue_calls[0], "subroutineName", "")) != "$q_initialize":
                return None
            if any(str(getattr(call, "subroutineName", "")) not in (
                    "$q_add", "$q_full", "$q_exam", "$q_remove")
                   for call in queue_calls[1:]):
                return None
            init = queue_calls[0]
            if (_literal_integral_value(init.arguments[1]) not in (1, 2)
                    or (_literal_integral_value(init.arguments[2]) or 0) <= 0
                    or any((_q_add_source_shape(call, instance)
                            if str(getattr(call, "subroutineName", "")) == "$q_add"
                            else (_q_full_source_shape(call)
                                  if str(getattr(call, "subroutineName", "")) == "$q_full"
                                  else (_q_exam_source_shape(call, instance)
                                        if str(getattr(call, "subroutineName", "")) == "$q_exam"
                                        else _q_remove_output_shape(call))))
                           is False for call in queue_calls[1:])):
                return None
        index = queue_calls.index(expression)
        if index == 1 and str(getattr(queue_calls[1], "subroutineName", "")) == "$q_initialize":
            status_value = 6
        elif qtype_value in (1, 2) and max_value > 0:
            status_value = 0
        elif qtype_value not in (1, 2):
            status_value = 4
        else:
            status_value = 5

        target, admitted = legacy_blocking_target(sm, output.left, True)
        if not admitted:
            return None
        width, two_state, reason = type_width_2s(output.left.type)
        if width is None or reason is not None:
            return None
        bits = format(status_value & ((1 << width) - 1), f"0{width}b")
        value = {"kind": "Literal", "span": node_span(sm, output.left),
                 "width": width, "bits": bits,
                 "q_initialize_status": status_value}
        if two_state:
            value = squash2_wrap(value, width)
        return {"kind": "BlockingAssign", "span": node_span(sm, expression),
                "target": target, "value": value,
                "q_initialize_status_lowered": status_value}
    except Exception:
        return None


def _q_add_status_call(sm, expression):
    """Lower the scalar status from a source-pure ``$q_add`` call.

    Only a literal queue ID and literal job/inform values are admitted.  The
    surrounding process must contain one valid literal ``$q_initialize`` and
    only source-ordered ``$q_add`` calls for that ID.  The flat self-check
    state then needs only the capacity counter: successful additions publish
    status 0 and the first addition after capacity publishes status 1.
    """
    try:
        if not _q_add_output_shape(expression):
            return None
        qid, _job, _inform, status = expression.arguments
        status_target, admitted = legacy_blocking_target(sm, status.left, True)
        if not admitted:
            return None

        receiver_scope = getattr(getattr(status.left, "symbol", None),
                                 "parentScope", None)
        instance = getattr(receiver_scope, "containingInstance", None)
        if instance is None:
            return None
        call_position = getattr(getattr(getattr(expression, "sourceRange", None),
                                        "start", None), "offset", -1)
        qid_value = _queue_history_literal(qid, instance, call_position)
        if qid_value is None:
            return None
        queue_calls = []

        def inspect(node):
            if (type(node).__name__ == "CallExpression"
                    and getattr(node, "isSystemCall", False)
                    and str(getattr(node, "subroutineName", "")).startswith("$q_")):
                queue_calls.append(node)

        instance.visit(inspect)
        queue_calls.sort(key=lambda node: getattr(
            getattr(getattr(node, "sourceRange", None), "start", None),
            "offset", -1))
        if not queue_calls or expression not in queue_calls:
            return None
        if str(getattr(queue_calls[0], "subroutineName", "")) != "$q_initialize":
            return None
        if any(str(getattr(call, "subroutineName", "")) not in (
                "$q_add", "$q_full", "$q_exam", "$q_remove")
               for call in queue_calls[1:]):
            return None
        init = queue_calls[0]
        init_position = getattr(getattr(getattr(init, "sourceRange", None),
                                        "start", None), "offset", -1)
        init_qid = _queue_history_literal(init.arguments[0], instance,
                                           init_position)
        if (len(init.arguments) != 4
                or init_qid != qid_value
                or _literal_integral_value(init.arguments[1]) not in (1, 2)
                or (_literal_integral_value(init.arguments[2]) or 0) <= 0):
            return None
        def valid_queue_call(call):
            name = str(getattr(call, "subroutineName", ""))
            shape = (_q_add_source_shape(call, instance)
                     if name == "$q_add"
                     else (_q_full_source_shape(call)
                           if name == "$q_full"
                           else (_q_exam_source_shape(call, instance)
                                 if name == "$q_exam"
                                 else _q_remove_output_shape(call))))
            call_position = getattr(getattr(getattr(call, "sourceRange", None),
                                             "start", None), "offset", -1)
            call_qid = _queue_history_literal(call.arguments[0], instance,
                                               call_position)
            return shape and call_qid == qid_value

        if any(not valid_queue_call(call) for call in queue_calls[1:]):
            return None
        index = queue_calls.index(expression)
        if index == 0:
            return None
        capacity = _literal_integral_value(init.arguments[2])
        prior_adds = sum(
            str(getattr(call, "subroutineName", "")) == "$q_add"
            for call in queue_calls[1:index])
        status_value = 0 if prior_adds < capacity else 1
        width, two_state, reason = type_width_2s(status.left.type)
        if width is None or reason is not None:
            return None
        value = {"kind": "Literal", "span": node_span(sm, status.left),
                 "width": width,
                 "bits": format(status_value & ((1 << width) - 1), f"0{width}b"),
                 "q_add_status": status_value}
        if two_state:
            value = squash2_wrap(value, width)
        return {"kind": "BlockingAssign", "span": node_span(sm, expression),
                "target": status_target, "value": value,
                "q_add_status_lowered": status_value}
    except Exception:
        return None


def _q_full_status_value(sm, expression):
    """Return the literal value of an admitted source-pure ``$q_full``."""
    try:
        if not _q_full_source_shape(expression):
            return None
        qid, status = expression.arguments
        qid_value = _literal_integral_value(qid)
        if qid_value is None:
            return None
        receiver_scope = getattr(getattr(status.left, "symbol", None),
                                 "parentScope", None)
        instance = getattr(receiver_scope, "containingInstance", None)
        if instance is None:
            return None
        queue_calls = []

        def inspect(node):
            if (type(node).__name__ == "CallExpression"
                    and getattr(node, "isSystemCall", False)
                    and str(getattr(node, "subroutineName", "")).startswith("$q_")):
                queue_calls.append(node)

        instance.visit(inspect)
        queue_calls.sort(key=lambda node: getattr(
            getattr(getattr(node, "sourceRange", None), "start", None),
            "offset", -1))
        if not queue_calls or expression not in queue_calls:
            return None
        if str(getattr(queue_calls[0], "subroutineName", "")) != "$q_initialize":
            return None
        if any(str(getattr(call, "subroutineName", "")) not in (
                "$q_add", "$q_full", "$q_exam")
               for call in queue_calls[1:]):
            return None
        init = queue_calls[0]
        if (len(init.arguments) != 4
                or _literal_integral_value(init.arguments[0]) != qid_value
                or _literal_integral_value(init.arguments[1]) not in (1, 2)
                or (_literal_integral_value(init.arguments[2]) or 0) <= 0):
            return None
        def valid_queue_call(call):
            name = str(getattr(call, "subroutineName", ""))
            shape = (_q_add_source_shape(call, instance)
                     if name == "$q_add"
                     else (_q_full_source_shape(call)
                           if name == "$q_full"
                           else _q_exam_source_shape(call, instance)))
            call_position = getattr(getattr(getattr(call, "sourceRange", None),
                                             "start", None), "offset", -1)
            call_qid = _queue_history_literal(call.arguments[0], instance,
                                               call_position)
            return shape and call_qid == qid_value

        if any(not valid_queue_call(call) for call in queue_calls[1:]):
            return None
        index = queue_calls.index(expression)
        if index == 0:
            return None
        capacity = _literal_integral_value(init.arguments[2])
        prior_adds = sum(
            str(getattr(call, "subroutineName", "")) == "$q_add"
            for call in queue_calls[1:index])
        status_value = 1 if prior_adds >= capacity else 0
        width, two_state, reason = type_width_2s(status.left.type)
        if width is None or reason is not None:
            return None
        return status_value, width, two_state
    except Exception:
        return None


def _q_full_status_call(sm, expression):
    """Lower a literal ``$q_full`` query to its scalar 0/1 status."""
    try:
        result = _q_full_status_value(sm, expression)
        if result is None:
            return None
        status_value, width, two_state = result
        status = expression.arguments[1]
        status_target, admitted = legacy_blocking_target(sm, status.left, True)
        if not admitted:
            return None
        value = {"kind": "Literal", "span": node_span(sm, status.left),
                 "width": width,
                 "bits": format(status_value & ((1 << width) - 1), f"0{width}b"),
                 "q_full_status": status_value}
        if two_state:
            value = squash2_wrap(value, width)
        return {"kind": "BlockingAssign", "span": node_span(sm, expression),
                "target": status_target, "value": value,
                "q_full_status_lowered": status_value}
    except Exception:
        return None


def _q_exam_status_call(sm, expression):
    """Lower literal queue length statistics from a source-pure ``$q_exam``.

    The admitted queue history contains one literal FIFO/LIFO initialization
    followed by literal ``$q_add``, nonempty ``$q_remove``, and statistic
    ``$q_exam`` calls.  A small source-order replay retains only payload
    occupancy, so current/max length remain exact without introducing a
    runtime queue object.  The four time statistics are zero for a history
    with no delay or event control; timed histories stay on the loud path.
    The task writes the statistic first and then status 0, matching the
    argument order and preserving the ordinary output-assignment semantics.
    """
    try:
        if not _q_exam_output_shape(expression):
            return None
        qid, stat_code, stat_value, status = expression.arguments
        stat_code_value = _literal_integral_value(stat_code)
        if stat_code_value not in (1, 2, 3, 4, 5, 6):
            return None
        stat_target, stat_admitted = legacy_blocking_target(sm, stat_value.left, True)
        status_target, status_admitted = legacy_blocking_target(sm, status.left, True)
        if not stat_admitted or not status_admitted:
            return None

        receiver_scope = getattr(getattr(stat_value.left, "symbol", None),
                                 "parentScope", None)
        instance = getattr(receiver_scope, "containingInstance", None)
        if instance is None:
            return None

        # The time columns (and, more generally, queue statistics) depend on
        # simulator time.  The replay below is deliberately the time-zero
        # slice; reject any delay/event/timing syntax in the enclosing
        # instance rather than manufacturing a timestamp.
        timed = False
        def inspect_timing(node):
            nonlocal timed
            name = type(node).__name__
            if (name in ("DelayControl", "TimedStatement", "TimingControl",
                         "EventControl", "SignalEventControl",
                         "CycleDelayControl", "ProceduralTimingControl")
                    or getattr(node, "timingControl", None) is not None):
                timed = True
        instance.visit(inspect_timing)
        if timed:
            return None
        expression_position = getattr(getattr(getattr(expression, "sourceRange", None),
                                              "start", None), "offset", -1)
        qid_value = _queue_history_literal(qid, instance, expression_position)
        if qid_value is None:
            return None
        queue_calls = []

        def inspect(node):
            if (type(node).__name__ == "CallExpression"
                    and getattr(node, "isSystemCall", False)
                    and str(getattr(node, "subroutineName", "")).startswith("$q_")):
                queue_calls.append(node)

        instance.visit(inspect)
        queue_calls.sort(key=lambda node: getattr(
            getattr(getattr(node, "sourceRange", None), "start", None),
            "offset", -1))
        if not queue_calls or expression not in queue_calls:
            return None
        if str(getattr(queue_calls[0], "subroutineName", "")) != "$q_initialize":
            return None
        if any(str(getattr(call, "subroutineName", "")) not in (
                "$q_add", "$q_remove", "$q_exam") for call in queue_calls[1:]):
            return None
        init = queue_calls[0]
        init_position = getattr(getattr(getattr(init, "sourceRange", None),
                                        "start", None), "offset", -1)
        init_qid = _queue_history_literal(init.arguments[0], instance,
                                           init_position)
        if (len(init.arguments) != 4
                or init_qid != qid_value
                or _literal_integral_value(init.arguments[1]) not in (1, 2)
                or (_literal_integral_value(init.arguments[2]) or 0) <= 0):
            return None

        def valid_queue_call(call):
            name = str(getattr(call, "subroutineName", ""))
            shape = (_q_add_source_shape(call, instance)
                     if name == "$q_add"
                     else (_q_exam_source_shape(call, instance)
                           if name == "$q_exam"
                           else _q_remove_output_shape(call)))
            call_position = getattr(getattr(getattr(call, "sourceRange", None),
                                             "start", None), "offset", -1)
            call_qid = _queue_history_literal(call.arguments[0], instance,
                                               call_position)
            return shape and call_qid == qid_value

        if any(not valid_queue_call(call) for call in queue_calls[1:]):
            return None
        index = queue_calls.index(expression)
        if index == 0:
            return None
        capacity = _literal_integral_value(init.arguments[2])
        if capacity is None or capacity <= 0:
            return None

        # Replay occupancy through the prefix.  A remove must be nonempty;
        # the payload lowering for that call writes the popped scalars, while
        # this recognizer needs only the queue length for the following exam.
        queue = []
        max_length = 0
        fifo = _literal_integral_value(init.arguments[1]) == 1
        for call in queue_calls[1:index]:
            name = str(getattr(call, "subroutineName", ""))
            if name == "$q_add":
                if len(queue) < capacity:
                    queue.append(None)
                max_length = max(max_length, len(queue))
            elif name == "$q_remove":
                if not _q_remove_output_shape(call) or not queue:
                    return None
                queue.pop(0 if fifo else -1)
            elif name == "$q_exam":
                if not _q_exam_source_shape(call, instance):
                    return None
            else:
                return None
        length = len(queue) if stat_code_value == 1 else (
            max_length if stat_code_value == 3 else 0)

        stat_width, stat_two_state, stat_reason = type_width_2s(stat_value.left.type)
        status_width, status_two_state, status_reason = type_width_2s(status.left.type)
        if (stat_width is None or stat_reason is not None
                or status_width is None or status_reason is not None):
            return None
        stat_literal = {"kind": "Literal", "span": node_span(sm, stat_value.left),
                        "width": stat_width,
                        "bits": format(length & ((1 << stat_width) - 1),
                                       f"0{stat_width}b"),
                        "q_exam_stat_value": length,
                        "q_exam_stat_code": stat_code_value}
        if stat_two_state:
            stat_literal = squash2_wrap(stat_literal, stat_width)
        status_literal = {"kind": "Literal", "span": node_span(sm, status.left),
                          "width": status_width,
                          "bits": format(0, f"0{status_width}b"),
                          "q_exam_status": 0}
        if status_two_state:
            status_literal = squash2_wrap(status_literal, status_width)
        return {
            "kind": "Block", "span": node_span(sm, expression),
            "stmts": [
                {"kind": "BlockingAssign", "span": node_span(sm, expression),
                 "target": stat_target, "value": stat_literal,
                 "q_exam_stat_value_lowered": length},
                {"kind": "BlockingAssign", "span": node_span(sm, expression),
                 "target": status_target, "value": status_literal,
                 "q_exam_status_lowered": 0},
            ],
            "q_exam_lowered": True,
            "q_exam_stat_code": stat_code_value,
            "q_exam_length": length,
        }
    except Exception:
        return None


def _q_full_value_call(sm, expression):
    """Lower a value-position ``$q_full`` with an unread status output."""
    try:
        result = _q_full_status_value(sm, expression)
        if result is None:
            return None
        status_value, width, two_state = result
        status = expression.arguments[1]
        target = getattr(status, "left", None)
        symbol = getattr(target, "symbol", None)
        if symbol is None:
            return None
        receiver_scope = getattr(getattr(target, "symbol", None),
                                 "parentScope", None)
        instance = getattr(receiver_scope, "containingInstance", None)
        if instance is None:
            return None
        allowed = set()

        def collect_outputs(node):
            if type(node).__name__ != "CallExpression" or not getattr(
                    node, "isSystemCall", False):
                return
            for argument in getattr(node, "arguments", []):
                if (type(argument).__name__ == "AssignmentExpression"
                        and type(getattr(argument, "right", None)).__name__
                        == "EmptyArgumentExpression"):
                    output = getattr(argument, "left", None)
                    source_range = getattr(output, "sourceRange", None)
                    allowed.add((
                        getattr(getattr(source_range, "start", None), "offset", None),
                        getattr(getattr(source_range, "end", None), "offset", None),
                    ))

        instance.visit(collect_outputs)
        q_full_offsets = []
        def collect_q_full(node):
            if (type(node).__name__ == "CallExpression"
                    and getattr(node, "isSystemCall", False)
                    and getattr(node, "subroutineName", "") == "$q_full"):
                source_range = getattr(node, "sourceRange", None)
                q_full_offsets.append(
                    getattr(getattr(source_range, "start", None), "offset", None))
        instance.visit(collect_q_full)
        first_q_full = min((offset for offset in q_full_offsets
                            if offset is not None), default=None)
        observed = False

        def inspect(node):
            nonlocal observed
            if (type(node).__name__ == "NamedValueExpression"
                    and getattr(node, "symbol", None) is symbol):
                node_range = getattr(node, "sourceRange", None)
                span = (
                    getattr(getattr(node_range, "start", None), "offset", None),
                    getattr(getattr(node_range, "end", None), "offset", None),
                )
                # The status output of q_full itself is intentionally not
                # represented by the value-position literal.  Reads before
                # the first q_full still observe the represented initializer
                # or add status, while any later read would observe an
                # unmodeled q_full status and must remain loud.
                before_first_q_full = (first_q_full is not None
                                       and span[0] is not None
                                       and span[0] < first_q_full)
                if span not in allowed and not before_first_q_full:
                    observed = True

        instance.visit(inspect)
        if observed:
            return None
        value = {"kind": "Literal", "span": node_span(sm, expression),
                 "width": width,
                 "bits": format(status_value & ((1 << width) - 1), f"0{width}b"),
                 "q_full_value": status_value}
        if two_state:
            value = squash2_wrap(value, width)
        return value
    except Exception:
        return None


def _q_remove_output_shape(expression):
    """Whether a queue removal has the ordinary three output lvalues."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$q_remove"
                or len(expression.arguments) != 4):
            return False
        _qid, job, inform, status = expression.arguments
        return (
            type(job).__name__ == "NamedValueExpression"
            and type(inform).__name__ == "AssignmentExpression"
            and inform.op is None
            and inform.timingControl is None
            and type(inform.right).__name__ == "EmptyArgumentExpression"
            and type(status).__name__ == "AssignmentExpression"
            and status.op is None
            and status.timingControl is None
            and type(status.right).__name__ == "EmptyArgumentExpression")
    except Exception:
        return False


def _q_remove_payload_call(sm, expression):
    """Lower a literal FIFO/LIFO queue add/remove history cellwise.

    The self-check state has no queue object, but a source-ordered history of
    literal adds and removes can be snapshot exactly: each removal becomes
    ordinary scalar writes to its job, inform, and status outputs.  The
    recognizer refuses branches, timing, computed payloads, capacity
    overflow, empty removals, and every other queue operation, so no dynamic
    queue semantics is guessed.
    """
    try:
        if not _q_remove_output_shape(expression):
            return None
        qid, job, inform, status = expression.arguments
        status_target, status_ok = legacy_blocking_target(sm, status.left, True)
        job_target, job_ok = legacy_blocking_target(sm, job, True)
        inform_target, inform_ok = legacy_blocking_target(sm, inform.left, True)
        if (not status_ok or not job_ok or not inform_ok
                or job_target.get("kind") != "Ident"
                or inform_target.get("kind") != "Ident"):
            return None
        receiver_scope = getattr(getattr(status.left, "symbol", None),
                                 "parentScope", None)
        instance = getattr(receiver_scope, "containingInstance", None)
        if instance is None:
            return None
        queue_calls = []

        def inspect(node):
            if (type(node).__name__ == "CallExpression"
                    and getattr(node, "isSystemCall", False)
                    and str(getattr(node, "subroutineName", "")).startswith("$q_")):
                queue_calls.append(node)

        instance.visit(inspect)
        queue_calls.sort(key=lambda node: getattr(
            getattr(getattr(node, "sourceRange", None), "start", None),
            "offset", -1))
        names = [str(getattr(node, "subroutineName", "")) for node in queue_calls]
        if not queue_calls or expression not in queue_calls:
            return None
        if names[0] != "$q_initialize" or any(
                name not in ("$q_add", "$q_remove", "$q_exam")
                for name in names[1:]):
            return None
        init = queue_calls[0]
        if (len(init.arguments) != 4
                or type(init.arguments[3]).__name__ != "AssignmentExpression"
                or _literal_integral_value(init.arguments[1]) not in (1, 2)):
            return None
        capacity = _literal_integral_value(init.arguments[2])
        if capacity is None or capacity <= 0:
            return None

        def position(node):
            return getattr(getattr(getattr(node, "sourceRange", None),
                                   "start", None), "offset", -1)

        qid_value = _queue_history_literal(qid, instance, position(expression))
        init_qid = _queue_history_literal(init.arguments[0], instance, position(init))
        if qid_value is None or init_qid != qid_value:
            return None

        def value_for(node, before):
            return _queue_history_literal(node, instance, before)

        def scalar_literal(node, value, marker):
            width, two_state, reason = type_width_2s(node.type)
            if width is None or reason is not None:
                return None
            literal = {"kind": "Literal", "span": node_span(sm, node),
                       "width": width,
                       "bits": format(value & ((1 << width) - 1), f"0{width}b"),
                       marker: value}
            return squash2_wrap(literal, width) if two_state else literal

        queue = []
        target_result = None
        for call in queue_calls:
            name = str(getattr(call, "subroutineName", ""))
            call_pos = position(call)
            call_qid = _queue_history_literal(call.arguments[0], instance, call_pos)
            if call_qid != qid_value:
                return None
            if name == "$q_initialize":
                continue
            if name == "$q_add":
                if not _q_add_source_shape(call, instance):
                    return None
                job_value = value_for(call.arguments[1], call_pos)
                inform_value = value_for(call.arguments[2], call_pos)
                if job_value is None or inform_value is None:
                    return None
                if len(queue) < capacity:
                    queue.append((job_value, inform_value))
                continue
            if name == "$q_exam":
                # A statistic query has no queue payload effect.  Validate
                # its source shape so this history cannot silently absorb a
                # computed, timed, or unsupported query.
                if not _q_exam_source_shape(call, instance):
                    return None
                continue
            if not _q_remove_output_shape(call):
                return None
            remove_job, remove_inform, remove_status = call.arguments[1:]
            if not queue:
                return None
            item = queue.pop(0 if _literal_integral_value(init.arguments[1]) == 1 else -1)
            if call is not expression:
                continue
            job_value, inform_value = item
            job_lit = scalar_literal(remove_job, job_value, "q_remove_job")
            inform_lit = scalar_literal(remove_inform.left, inform_value, "q_remove_inform")
            status_lit = scalar_literal(remove_status.left, 0, "q_remove_status")
            if job_lit is None or inform_lit is None or status_lit is None:
                return None
            target_result = {
                "kind": "Block", "span": node_span(sm, expression),
                "stmts": [
                    {"kind": "BlockingAssign", "span": node_span(sm, expression),
                     "target": job_target, "value": job_lit},
                    {"kind": "BlockingAssign", "span": node_span(sm, expression),
                     "target": inform_target, "value": inform_lit},
                    {"kind": "BlockingAssign", "span": node_span(sm, expression),
                     "target": status_target, "value": status_lit},
                ],
                "q_remove_payload_lowered": True,
            }
        return target_result
    except Exception:
        return None


def _q_remove_status_call(sm, expression):
    """Lower queue-removal status codes with no represented queue payload.

    IEEE 1800-2023 §20.15.6 reports status 2 for an undefined queue ID and
    status 3 when a valid, newly initialized queue is empty.  The self-check
    state can retain that scalar status while leaving the job and inform
    outputs opaque, provided neither output is read later and no add/remove
    operation exposes queue contents.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "$q_remove"
                or len(expression.arguments) != 4):
            return None
        qid, job, inform, status = expression.arguments
        if (type(inform).__name__ != "AssignmentExpression"
                or inform.op is not None
                or inform.timingControl is not None
                or type(inform.right).__name__ != "EmptyArgumentExpression"
                or type(status).__name__ != "AssignmentExpression"
                or status.op is not None
                or status.timingControl is not None
                or type(status.right).__name__ != "EmptyArgumentExpression"):
            return None
        if not _case_source_expression_ok(qid):
            return None
        status_target, admitted = legacy_blocking_target(sm, status.left, True)
        if not admitted:
            return None
        job_target, job_admitted = legacy_blocking_target(sm, job, True)
        inform_target, inform_admitted = legacy_blocking_target(sm, inform.left, True)
        if (not job_admitted or not inform_admitted
                or job_target.get("kind") != "Ident"
                or inform_target.get("kind") != "Ident"):
            return None

        receiver_scope = getattr(getattr(status.left, "symbol", None),
                                 "parentScope", None)
        instance = getattr(receiver_scope, "containingInstance", None)
        if instance is None:
            return None
        queue_calls = []
        def inspect(node):
            if (type(node).__name__ == "CallExpression"
                    and getattr(node, "isSystemCall", False)
                    and str(getattr(node, "subroutineName", "")).startswith("$q_")):
                queue_calls.append(node)
        instance.visit(inspect)
        queue_calls.sort(key=lambda node: getattr(
            getattr(getattr(node, "sourceRange", None), "start", None),
            "offset", -1))
        names = [str(getattr(node, "subroutineName", "")) for node in queue_calls]
        if names == ["$q_remove"]:
            status_value = 2
            qid_value = _literal_integral_value(qid)
            if qid_value is None:
                return None
        elif names == ["$q_initialize", "$q_remove"]:
            init = queue_calls[0]
            init_qid = init.arguments[0]
            init_value = _literal_integral_value(init_qid)
            if init_value is None and type(init_qid).__name__ == "NamedValueExpression":
                symbol = getattr(init_qid, "symbol", None)
                if symbol is None or getattr(symbol, "initializer", None) is not None:
                    return None
                assignments = []
                invalid = False
                def inspect_assignment(node):
                    nonlocal invalid
                    if type(node).__name__ != "AssignmentExpression":
                        return
                    left = getattr(node, "left", None)
                    if getattr(left, "symbol", None) is not symbol:
                        return
                    if (getattr(node, "op", None) is not None
                            or getattr(node, "timingControl", None) is not None
                            or getattr(node, "isNonBlocking", False)):
                        invalid = True
                        return
                    value = _literal_integral_value(getattr(node, "right", None))
                    if value is None:
                        invalid = True
                        return
                    assignments.append((getattr(getattr(getattr(node, "sourceRange", None),
                                                        "start", None), "offset", -1), value))
                instance.visit(inspect_assignment)
                if invalid or len(assignments) != 1:
                    return None
                init_pos = getattr(getattr(getattr(init, "sourceRange", None),
                                           "start", None), "offset", -1)
                prior = [value for position, value in assignments if position < init_pos]
                init_value = prior[0] if len(prior) == 1 else None
            remove_value = _literal_integral_value(qid)
            if remove_value is None and type(qid).__name__ == "NamedValueExpression":
                remove_value = init_value
            if (init_value is None or remove_value != init_value
                    or _literal_integral_value(init.arguments[1]) not in (1, 2)
                    or (_literal_integral_value(init.arguments[2]) or 0) <= 0):
                return None
            status_value = 3
        else:
            return None

        # Job and inform are intentionally opaque, but stale reads would make
        # a status-only lowering unsound.  Permit only their output positions.
        observed = {getattr(job, "symbol", None), getattr(inform.left, "symbol", None)}
        def span(node):
            source_range = getattr(node, "sourceRange", None)
            start = getattr(getattr(source_range, "start", None), "offset", None)
            end = getattr(getattr(source_range, "end", None), "offset", None)
            return (start, end)
        allowed_spans = {span(job), span(inform.left)}
        unsafe = False
        def inspect_reads(node):
            nonlocal unsafe
            if (type(node).__name__ == "NamedValueExpression"
                    and getattr(node, "symbol", None) in observed
                    and span(node) not in allowed_spans):
                unsafe = True
        instance.visit(inspect_reads)
        if unsafe:
            return None
        width, two_state, reason = type_width_2s(status.left.type)
        if width is None or reason is not None:
            return None
        value = {"kind": "Literal", "span": node_span(sm, status.left),
                 "width": width, "bits": format(status_value & ((1 << width) - 1), f"0{width}b"),
                 "q_remove_status": status_value}
        if two_state:
            value = squash2_wrap(value, width)
        return {"kind": "BlockingAssign", "span": node_span(sm, expression),
                "target": status_target, "value": value,
                "q_remove_status_lowered": status_value}
    except Exception:
        return None


def _fixed_array_reverse_method(sm, expression):
    """Lower ``reverse()`` on a one-dimensional fixed array.

    The flat self-check state stores each leaf independently.  Besides a
    complete declaration initializer, a source-ordered literal pattern write
    and a copy from another such array can therefore provide the aggregate
    snapshot needed by ``reverse()``.  Earlier reversals are replayed in source
    order, so a second call sees the first mutation.  Every other aggregate
    operation remains loud; in particular, no branch or loop is treated as a
    static assignment sequence.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "reverse"
                or len(expression.arguments) != 1):
            return None
        receiver = expression.arguments[0]
        if type(receiver).__name__ != "NamedValueExpression":
            return None
        symbol = getattr(receiver, "symbol", None)
        if symbol is None:
            return None
        shape = _fixed_array_dimensions(receiver.type, max_cells=128)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        if len(dimensions) != 1:
            return None
        left, right = dimensions[0]
        count = abs(right - left) + 1
        width, two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None or count <= 0:
            return None
        root = _array_storage_name(symbol)
        positions = list(range(left, right + (1 if right >= left else -1),
                               1 if right >= left else -1))
        instance = symbol.parentScope.containingInstance
        if instance is None:
            return None

        def source_offset(node):
            return getattr(getattr(getattr(node, "sourceRange", None),
                                   "start", None), "offset", None)

        def array_root(expression_node):
            shape = _fixed_array_assignment_shape(expression_node)
            if shape is not None:
                return shape[0]
            current = expression_node
            while type(current).__name__ == "ElementSelectExpression":
                current = getattr(current, "value", None)
            if (_storage_expression(current)
                    and type(current.type.canonicalType).__name__ ==
                    "FixedSizeUnpackedArrayType"):
                try:
                    return _array_storage_name(current.symbol)
                except Exception:
                    return None
            return None

        def contains_ident(node):
            if isinstance(node, dict):
                return node.get("kind") == "Ident" or any(
                    contains_ident(value) for value in node.values())
            if isinstance(node, list):
                return any(contains_ident(value) for value in node)
            return False

        operations = []
        control_ranges = []
        root_symbols = {root: symbol}
        valid = True

        def inspect(node):
            nonlocal valid
            kind = type(node).__name__
            offset = source_offset(node)
            if offset is None:
                return
            if any(token in kind for token in (
                    "Conditional", "Case", "For", "While", "Repeat",
                    "Foreach", "Forever", "Wait", "Fork")):
                end = getattr(getattr(getattr(node, "sourceRange", None),
                                      "end", None), "offset", None)
                if end is not None:
                    control_ranges.append((offset, end))
            if kind == "AssignmentExpression":
                lhs_node = getattr(node, "left", None)
                lhs_root = array_root(lhs_node)
                if lhs_root is not None:
                    lhs_symbol = getattr(lhs_node, "symbol", None)
                    if lhs_symbol is not None:
                        root_symbols.setdefault(lhs_root, lhs_symbol)
                    lowered = (_fixed_array_pattern_assignment(sm, node)
                               or _fixed_array_copy_assignment(sm, node))
                    rhs_node = getattr(node, "right", None)
                    rhs_root = array_root(rhs_node)
                    rhs_symbol = getattr(rhs_node, "symbol", None)
                    while (rhs_symbol is None
                           and type(rhs_node).__name__ == "ConversionExpression"):
                        rhs_node = getattr(rhs_node, "operand", None)
                        rhs_symbol = getattr(rhs_node, "symbol", None)
                    if rhs_root is not None and rhs_symbol is not None:
                        root_symbols.setdefault(rhs_root, rhs_symbol)
                    operations.append({
                        "kind": "assign" if lowered is not None else "invalid",
                        "offset": offset,
                        "lhs": lhs_root,
                        "rhs": rhs_root,
                        "lowered": lowered,
                    })
                    # Whole-array assignments are inspected as one unit; the
                    # child NamedValueExpressions are not aggregate uses.
                    if lowered is not None:
                        return VisitAction.Skip
            elif kind == "CallExpression":
                name = str(getattr(node, "subroutineName", ""))
                arguments = getattr(node, "arguments", [])
                if (len(arguments) == 1
                        and type(arguments[0]).__name__ == "NamedValueExpression"):
                    call_root = array_root(arguments[0])
                    if call_root is not None:
                        root_symbols.setdefault(call_root,
                                                 getattr(arguments[0], "symbol", None))
                        if name in ("reverse", "sort", "rsort"):
                            operations.append({
                                "kind": ("reverse" if name == "reverse"
                                         else "other-call"),
                                "offset": offset,
                                "lhs": call_root,
                                "rhs": None,
                                "lowered": None,
                            })
                            # The receiver itself is handled by the operation
                            # walk; do not count it as a whole-array use.
                            return VisitAction.Skip
            if kind == "ElementSelectExpression":
                value = getattr(node, "value", None)
                if (type(value).__name__ == "NamedValueExpression"
                        and getattr(value, "symbol", None) is symbol):
                    if _constant_dimension_selector(
                            getattr(node, "selector", None)) is None:
                        valid = False
                    return VisitAction.Skip
            if kind in ("NamedValueExpression", "HierarchicalValueExpression"):
                if (getattr(node, "symbol", None) is symbol
                        and node is not receiver):
                    valid = False

        instance.visit(inspect)
        if not valid:
            return None

        current_offset = source_offset(expression)
        if current_offset is None:
            return None
        control_ranges = list(set(control_ranges))
        if any(start < current_offset < end for start, end in control_ranges):
            return None
        operations.sort(key=lambda operation: operation["offset"])
        before = [operation for operation in operations
                  if operation["offset"] < current_offset]

        # Follow only whole-array copies that feed the receiver.  This keeps
        # unrelated arrays (including an independently sorted sibling) out of
        # the state proof while still requiring every source cell of a copy to
        # be known.
        needed = {root}
        changed = True
        while changed:
            changed = False
            for operation in before:
                if (operation["kind"] == "assign"
                        and operation["lhs"] in needed
                        and operation["rhs"] is not None
                        and operation["rhs"] not in needed):
                    needed.add(operation["rhs"])
                    changed = True
        if any(operation["kind"] in ("invalid", "other-call") and (
                operation["lhs"] in needed or operation["rhs"] in needed)
                for operation in operations):
            return None
        if any(any(start < operation["offset"] < end
                   for start, end in control_ranges)
               and (operation["lhs"] in needed or operation["rhs"] in needed)
               for operation in before):
            return None

        array_positions = {}

        def state_for(name):
            array_symbol = root_symbols.get(name)
            if array_symbol is None:
                return None
            array_shape = _fixed_array_dimensions(array_symbol.type, max_cells=128)
            if array_shape is None or len(array_shape[0]) != 1:
                return None
            array_dimensions, array_leaf = array_shape
            array_left, array_right = array_dimensions[0]
            own_positions = list(range(
                array_left,
                array_right + (1 if array_right >= array_left else -1),
                1 if array_right >= array_left else -1))
            if len(own_positions) != count:
                return None
            array_width, _array_two, array_reason = type_width_2s(array_leaf)
            if array_width != width or array_reason is not None:
                return None
            array_positions[name] = own_positions
            array_values = _fixed_array_initializer_values(
                sm, getattr(array_symbol, "initializer", None), name,
                array_width, len(own_positions))
            if array_values is None or any(contains_ident(value)
                                           for value in array_values):
                return None
            return {position: value for position, value
                    in zip(own_positions, array_values)}

        states = {name: state_for(name) for name in needed}
        if any(state is None for state in states.values()):
            return None

        def cell_position(name, array_name):
            prefix = array_name + "["
            if (not isinstance(name, str) or not name.startswith(prefix)
                    or not name.endswith("]")):
                return None
            try:
                position = int(name[len(prefix):-1])
            except (TypeError, ValueError):
                return None
            return position if position in array_positions.get(array_name, ()) else None

        def resolve_value(value, source_states):
            if isinstance(value, dict):
                if value.get("kind") == "Ident":
                    name = value.get("name")
                    for source_name, source_state in source_states.items():
                        position = cell_position(name, source_name)
                        if position is not None:
                            return source_state.get(position)
                    return None
                return {key: resolve_value(child, source_states)
                        for key, child in value.items()}
            if isinstance(value, list):
                return [resolve_value(child, source_states) for child in value]
            return value

        for operation in before:
            if operation["lhs"] not in needed:
                continue
            name = operation["lhs"]
            if operation["kind"] == "reverse":
                current = states[name]
                order = array_positions[name]
                if any(current.get(position) is None for position in order):
                    return None
                states[name] = {
                    position: value for position, value in zip(
                        order, reversed([current[position] for position in order]))}
                continue
            if operation["kind"] != "assign":
                return None
            lowered = operation["lowered"]
            if lowered is None:
                return None
            source_states = {source: states[source] for source in needed
                             if states.get(source) is not None}
            pending = {}
            for statement in lowered.get("stmts", []):
                target_name = statement.get("target", {}).get("name")
                position = cell_position(target_name, name)
                value = resolve_value(statement.get("value"), source_states)
                if position is None or value is None or contains_ident(value):
                    return None
                pending[position] = value
            if set(pending) != set(array_positions[name]):
                return None
            states[name] = pending

        values = [states[root][position] for position in positions]
        if any(value is None for value in values):
            return None

        reversed_values = list(reversed(values))
        statements = []
        for position, value in zip(positions, reversed_values):
            if two_state:
                value = squash2_wrap(value, width)
            statements.append({
                "kind": "BlockingAssign",
                "span": node_span(sm, expression),
                "target": {"kind": "Ident", "span": node_span(sm, receiver),
                           "width": width,
                           "name": f"{symbol.name}[{position}]"},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expression),
                "stmts": statements, "fixed_array_reverse_lowered": True}
    except Exception:
        return None


def _literal_array_order_key(value, width, signed):
    """Return the integral ordering key for a fully known lowered value."""
    node = value
    while isinstance(node, dict) and node.get("kind") == "Squash2":
        node = node.get("operand")
    if isinstance(node, dict) and node.get("kind") == "Unary":
        if node.get("op") not in ("+", "-"):
            return None
        inner = _literal_array_order_key(node.get("operand"), width, signed)
        if inner is None:
            return None
        return -inner if node.get("op") == "-" else inner
    if (not isinstance(node, dict) or node.get("kind") != "Literal"
            or node.get("width") != width):
        return None
    bits = node.get("bits")
    if (not isinstance(bits, str) or len(bits) != width
            or any(bit not in "01" for bit in bits)):
        return None
    result = int(bits, 2)
    if signed and bits[0] == "1":
        result -= 1 << width
    return result


def _fixed_array_ordering_method(sm, expression):
    """Lower ``sort()``/``rsort()`` for a finite literal integral array.

    The flat state can represent the resulting order exactly when every cell
    value is known before the method call.  Fixed arrays use their complete
    literal initializer; sampled dynamic arrays use one blocking literal write
    per cell after a constant ``new[N]`` allocation.  Whole-array aliases,
    with-clauses, unknown values, and any other receiver use remain loud.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName not in ("sort", "rsort")
                or len(expression.arguments) != 1):
            return None
        receiver = expression.arguments[0]
        if type(receiver).__name__ != "NamedValueExpression":
            return None
        symbol = getattr(receiver, "symbol", None)
        if symbol is None:
            return None
        array_type = getattr(receiver.type, "canonicalType", receiver.type)
        kind = type(array_type).__name__
        if kind == "FixedSizeUnpackedArrayType":
            shape = _fixed_array_dimensions(array_type, max_cells=128)
            if shape is None:
                return None
            dimensions, leaf_type = shape
            if len(dimensions) != 1:
                return None
            left, right = dimensions[0]
            count = abs(right - left) + 1
            dynamic = False
        elif kind == "DynamicArrayType":
            count = _dynamic_array_constant_extent(symbol)
            if count is None or count <= 0 or count > 128:
                return None
            left, right = 0, count - 1
            leaf_type = array_type.elementType
            dynamic = True
        else:
            return None
        width, two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None or count <= 0:
            return None

        # No whole-array read, alias, or second ordering operation may observe
        # the opaque aggregate. Constant element reads remain valid after the
        # lowered cell writes; the allocation itself is the only whole-array
        # expression admitted for a dynamic receiver.
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        if instance is None or not source:
            return None
        call_start = getattr(getattr(expression, "sourceRange", None),
                             "start", None)
        call_start = getattr(call_start, "offset", None)
        if call_start is None:
            return None
        valid = True

        def inspect_uses(node):
            nonlocal valid
            node_kind = type(node).__name__
            if node_kind == "AssignmentExpression":
                # Whole-array pattern/copy assignments are lowered to the
                # flat cells below.  Skip their aggregate children so the
                # source array read in a copy is not mistaken for an opaque
                # alias use.
                lhs = getattr(node, "left", None)
                if (_storage_expression(lhs)
                        and getattr(lhs, "symbol", None) is symbol
                        and (_fixed_array_pattern_assignment(sm, node)
                             or _fixed_array_copy_assignment(sm, node))):
                    return VisitAction.Skip
                if _fixed_array_pattern_assignment(sm, node):
                    return VisitAction.Skip
                if _fixed_array_copy_assignment(sm, node):
                    return VisitAction.Skip
            if node_kind == "CallExpression":
                arguments = getattr(node, "arguments", [])
                if (len(arguments) == 1
                        and type(arguments[0]).__name__ == "NamedValueExpression"
                        and getattr(arguments[0], "symbol", None) is symbol):
                    name = str(getattr(node, "subroutineName", ""))
                    if name in ("sort", "rsort"):
                        return VisitAction.Skip
                    valid = False
                    return VisitAction.Skip
            if node_kind == "ElementSelectExpression":
                value = getattr(node, "value", None)
                if (type(value).__name__ == "NamedValueExpression"
                        and getattr(value, "symbol", None) is symbol):
                    if _constant_dimension_selector(getattr(node, "selector", None)) is None:
                        valid = False
                    return VisitAction.Skip
            if node_kind != "NamedValueExpression" or getattr(node, "symbol", None) is not symbol:
                return
            if node is receiver:
                return
            end = getattr(getattr(node, "sourceRange", None), "end", None)
            end = getattr(end, "offset", None)
            suffix = source[end:].lstrip() if end is not None else ""
            # A sampled dynamic allocation is the one whole-array write that
            # creates the flat cells. Declarations have no such expression.
            if dynamic and re.match(r"(?:=\s*)?new\s*\[", suffix):
                return
            valid = False

        instance.visit(inspect_uses)
        if not valid:
            return None

        values = None
        initializer = getattr(symbol, "initializer", None)
        if initializer is not None:
            values = _fixed_array_initializer_values(
                sm, initializer, _array_storage_name(symbol), width, count)

        if not dynamic:
            # A fixed array may be initialized procedurally with one literal
            # assignment pattern before sorting. Replay that assignment and
            # any earlier sort/rsort calls so repeated ordering observes the
            # preceding mutation exactly.
            operations = []

            def inspect_fixed_operations(node):
                nonlocal valid
                offset = getattr(getattr(getattr(node, "sourceRange", None),
                                          "start", None), "offset", None)
                if offset is None or offset >= call_start:
                    return
                kind = type(node).__name__
                if kind == "AssignmentExpression":
                    lhs = getattr(node, "left", None)
                    if (_storage_expression(lhs)
                            and getattr(lhs, "symbol", None) is symbol):
                        lowered = _fixed_array_pattern_assignment(sm, node)
                        if lowered is not None:
                            operations.append((offset, "assign", lowered))
                        else:
                            valid = False
                    elif (type(lhs).__name__ == "ElementSelectExpression"
                          and type(getattr(lhs, "value", None)).__name__ ==
                          "NamedValueExpression"
                          and getattr(lhs.value, "symbol", None) is symbol):
                        # A direct cell write before ordering would change
                        # the aggregate snapshot; do not silently sort the
                        # declaration initializer instead.
                        valid = False
                elif kind == "CallExpression":
                    arguments = getattr(node, "arguments", [])
                    if (len(arguments) == 1
                            and type(arguments[0]).__name__ ==
                            "NamedValueExpression"
                            and getattr(arguments[0], "symbol", None) is symbol):
                        name = str(getattr(node, "subroutineName", ""))
                        if name in ("sort", "rsort"):
                            operations.append((offset, name, None))

            instance.visit(inspect_fixed_operations)
            operations.sort(key=lambda item: item[0])

            def lowered_values(lowered):
                result = []
                for statement in lowered.get("stmts", []):
                    value = statement.get("value")
                    if value is None:
                        return None
                    result.append(value)
                return result if len(result) == count else None

            if values is None:
                for _offset, operation, lowered in operations:
                    if operation == "assign":
                        values = lowered_values(lowered)
                    elif operation in ("sort", "rsort"):
                        if values is None:
                            valid = False
                            break
                        keyed = []
                        for value in values:
                            key = _literal_array_order_key(
                                value, width, bool(leaf_type.isSigned))
                            if key is None:
                                valid = False
                                break
                            keyed.append((key, value))
                        if not valid:
                            break
                        values = [value for _key, value in sorted(
                            keyed, key=lambda item: item[0],
                            reverse=operation == "rsort")]
            else:
                for _offset, operation, lowered in operations:
                    if operation == "assign":
                        values = lowered_values(lowered)
                    elif operation in ("sort", "rsort"):
                        keyed = []
                        for value in values:
                            key = _literal_array_order_key(
                                value, width, bool(leaf_type.isSigned))
                            if key is None:
                                valid = False
                                break
                            keyed.append((key, value))
                        if not valid:
                            break
                        values = [value for _key, value in sorted(
                            keyed, key=lambda item: item[0],
                            reverse=operation == "rsort")]

            if not valid or values is None:
                return None

        if values is None:
            # Dynamic arrays without a declaration initializer are admitted
            # only when every cell has exactly one preceding literal write.
            assignments = {}

            def inspect_assignments(node):
                if type(node).__name__ != "AssignmentExpression":
                    return
                start = getattr(getattr(node, "sourceRange", None), "start", None)
                start = getattr(start, "offset", None)
                if start is None or start >= call_start:
                    return
                lhs = getattr(node, "left", None)
                if type(lhs).__name__ != "ElementSelectExpression":
                    return
                base = getattr(lhs, "value", None)
                if (type(base).__name__ != "NamedValueExpression"
                        or getattr(base, "symbol", None) is not symbol):
                    return
                position = _constant_dimension_selector(getattr(lhs, "selector", None))
                if position is None or position < 0 or position >= count:
                    return
                if (node.op is not None or node.isNonBlocking
                        or node.timingControl is not None):
                    assignments[position] = None
                    return
                if not _case_source_expression_ok(node.right, packed_members=True):
                    assignments[position] = None
                    return
                value = convert_expr(sm, node.right)
                if (value is None or value.get("kind") == "Unsupported"
                        or width_of(value) != width
                        or not _case_expression_ok(value)):
                    assignments[position] = None
                    return
                # Duplicate writes make source-order execution observable;
                # require one assignment per cell in this static slice.
                if position in assignments:
                    assignments[position] = None
                else:
                    assignments[position] = value

            instance.visit(inspect_assignments)
            if (set(assignments) != set(range(count))
                    or any(value is None for value in assignments.values())):
                return None
            values = [assignments[position] for position in range(count)]

        if (values is None or len(values) != count
                or any(value is None for value in values)):
            return None
        keyed = []
        for value in values:
            key = _literal_array_order_key(value, width, bool(leaf_type.isSigned))
            if key is None:
                return None
            keyed.append((key, value))
        ordered = [value for _key, value in sorted(
            keyed, key=lambda item: item[0],
            reverse=expression.subroutineName == "rsort")]
        step = 1 if right >= left else -1
        statements = []
        for position, value in zip(range(left, right + step, step), ordered):
            if two_state:
                value = squash2_wrap(value, width)
            statements.append({
                "kind": "BlockingAssign",
                "span": node_span(sm, expression),
                "target": {"kind": "Ident", "span": node_span(sm, receiver),
                           "width": width,
                           "name": f"{_array_storage_name(symbol)}[{position}]"},
                "value": value,
            })
        return {"kind": "Block", "span": node_span(sm, expression),
                "stmts": statements,
                "fixed_array_ordering_lowered": expression.subroutineName}
    except Exception:
        return None


def _literal_integral_value(expression):
    """Read a small literal integral expression without evaluating source code.

    ``getc`` only needs a scalar index.  Keep this deliberately narrower than
    the general constant folder: integer literals, their implicit conversions,
    and unary plus/minus are the complete admitted surface.  X/Z bits and
    every named or computed expression remain outside the self-check state.
    """
    node = expression
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return None
    if type(node).__name__ in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
        try:
            sv = node.value
            bits = svint_bits(sv)
            if not bits or any(bit not in "01" for bit in bits):
                return None
            value = int(bits, 2)
            if node.type.isSigned and bits[0] == "1":
                value -= 1 << len(bits)
            return value
        except Exception:
            return None
    if type(node).__name__ == "UnaryExpression":
        op = str(getattr(node, "op", "")).split(".")[-1]
        if op not in ("Plus", "Minus", "UnaryPlus", "UnaryMinus"):
            return None
        value = _literal_integral_value(getattr(node, "operand", None))
        if value is None:
            return None
        return -value if op in ("Minus", "UnaryMinus") else value
    return None


def _stdout_descriptor_variable(sm, expression):
    """Return a predefined stdout MCD assigned immediately before a call.

    IEEE 1800-2023 §21.3.1 permits a descriptor variable to carry the
    predefined stdout MCD (bit 0, or ``32'h8000_0001``).  The flat self-check
    state has no file-descriptor object, so admit only the source-pure shape
    that can be replaced by the existing literal descriptor: a 32-bit
    integral variable, exactly one direct blocking literal assignment in the
    same initial block before this call, and no other read or write of that
    variable.  Conditional, aliased, selected, nonblocking, timed, and
    computed forms stay loud rather than guessing a descriptor's runtime
    history.
    """
    try:
        if type(expression).__name__ != "NamedValueExpression":
            return None
        symbol = getattr(expression, "symbol", None)
        if (symbol is None
                or str(getattr(symbol, "kind", "")).split(".")[-1] != "Variable"
                or not getattr(expression.type, "isIntegral", False)
                or getattr(expression.type, "bitWidth", None) != 32
                or getattr(symbol, "initializer", None) is not None):
            return None
        call_start = getattr(getattr(getattr(expression, "sourceRange", None),
                                     "start", None), "offset", None)
        if call_start is None:
            return None
        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        if instance is None:
            return None

        # Keep the call and assignment in one direct initial-block statement
        # list.  This excludes writes hidden behind branches, loops, or a
        # different process whose execution order the time-zero surface does
        # not model.
        def source_range(node):
            sr = getattr(node, "sourceRange", None)
            start = getattr(getattr(sr, "start", None), "offset", None)
            end = getattr(getattr(sr, "end", None), "offset", None)
            return (start, end) if start is not None and end is not None else None

        direct_expressions = {}
        def inspect_process(node):
            if type(node).__name__ != "ProceduralBlockSymbol":
                return
            syntax = getattr(node, "syntax", None)
            if str(getattr(syntax, "kind", "")).split(".")[-1] != "InitialBlock":
                return
            body = getattr(node, "body", None)
            if str(getattr(body, "kind", "")).split(".")[-1] != "Block":
                return
            sequence = getattr(getattr(body, "body", None), "list", None)
            if sequence is None:
                return
            for statement in sequence:
                if type(statement).__name__ == "ExpressionStatement":
                    value = getattr(statement, "expr", None)
                    if value is not None:
                        span = source_range(value)
                        if span is not None:
                            direct_expressions[span] = id(node)
        instance.visit(inspect_process)
        argument_span = source_range(expression)
        if argument_span is None:
            return None
        call_processes = {
            process for (start, end), process in direct_expressions.items()
            if start <= argument_span[0] < end
        }
        if len(call_processes) != 1:
            return None
        call_process = next(iter(call_processes))

        assignments = []
        all_references = []
        all_writes = []
        def inspect(node):
            kind = type(node).__name__
            if kind in ("NamedValueExpression", "HierarchicalValueExpression"):
                if getattr(node, "symbol", None) is symbol:
                    span = source_range(node)
                    if span is not None:
                        all_references.append(span)
                return
            if kind != "AssignmentExpression":
                return
            left = getattr(node, "left", None)
            if left is None:
                return
            # A selected/compound assignment still contains a reference to
            # the descriptor variable and is therefore a write we reject.
            references = []
            def inspect_left(child):
                if (type(child).__name__ in
                        ("NamedValueExpression", "HierarchicalValueExpression")
                        and getattr(child, "symbol", None) is symbol):
                    references.append(child)
            left.visit(inspect_left)
            if references:
                all_writes.append(node)
            left_span = source_range(left)
            node_span_key = source_range(node)
            if (len(references) != 1 or left_span != source_range(references[0])
                    or node_span_key not in direct_expressions
                    or direct_expressions[node_span_key] != call_process
                    or getattr(node, "op", None) is not None
                    or getattr(node, "timingControl", None) is not None
                    or getattr(node, "isNonBlocking", False)):
                return
            start = getattr(getattr(getattr(node, "sourceRange", None),
                                    "start", None), "offset", None)
            if start is None or start >= call_start:
                return
            rhs = getattr(node, "right", None)
            if not _integral_literal_source(rhs):
                return
            value = convert_expr(sm, rhs)
            if (value is None or value.get("kind") != "Literal"
                    or value.get("width") != 32):
                return
            bits = value.get("bits", "")
            if not bits or any(bit not in "01" for bit in bits):
                return
            assignments.append((node, int(bits, 2)))
        instance.visit(inspect)

        if len(assignments) != 1 or len(all_writes) != 1:
            return None
        assignment, descriptor = assignments[0]
        if descriptor not in (1, 0x80000001):
            return None
        # The only permitted references are the assignment's LHS and this
        # call's descriptor argument.  Any extra read could observe a value
        # that the literal replacement would erase.
        allowed = {source_range(assignment.left), argument_span}
        if any(reference not in allowed for reference in all_references):
            return None
        if (source_range(assignment) not in direct_expressions
                or direct_expressions[source_range(assignment)] != call_process):
            return None
        return descriptor
    except Exception:
        return None


def _string_literal_getc_method(expression):
    """Recognize ``getc`` on a source-pure ASCII string literal.

    SystemVerilog returns a zero byte for a negative or out-of-range index.
    The flat self-check state has no string storage, so this admits only the
    scalar fact available from a declaration or a direct blocking literal
    assignment.  ``_string_literal_source_value`` performs the source-order
    history check and selects the latest assignment before the query; dynamic
    writes, aliases, non-ASCII literals, and other observations remain loud.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "getc"):
            return False
        arguments = list(expression.arguments)
        if len(arguments) != 2 or type(arguments[0]).__name__ != "NamedValueExpression":
            return False
        if _literal_integral_value(arguments[1]) is None:
            return False
        return _string_literal_source_value(expression, "getc") is not None
    except Exception:
        return False


def _string_literal_case_method(expression):
    """Recognize a discarded case conversion on a proven ASCII string.

    ``toupper`` and ``tolower`` return a fresh string and have no represented
    state effect when their result is discarded.  Keep the receiver history
    check identical to the other literal-string queries; non-ASCII, dynamic,
    aliased, and mutated strings remain outside the flat self-check state.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName not in ("toupper", "tolower")
                or len(expression.arguments) != 1
                or type(expression.arguments[0]).__name__ != "NamedValueExpression"):
            return False
        return _string_literal_source_value(
            expression, expression.subroutineName) is not None
    except Exception:
        return False


def _string_literal_substr_method(expression):
    """Recognize ``substr`` on a proven ASCII string and literal bounds."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "substr"
                or len(expression.arguments) != 3
                or type(expression.arguments[0]).__name__ != "NamedValueExpression"
                or _literal_integral_value(expression.arguments[1]) is None
                or _literal_integral_value(expression.arguments[2]) is None):
            return False
        return _string_literal_source_value(expression, "substr") is not None
    except Exception:
        return False


def _string_literal_index_value(expression):
    """Return the byte selected from a source-pure ASCII string.

    Direct ``s[i]`` indexing has the same literal history boundary as
    ``s.getc(i)``: the receiver must be initialized or assigned from an ASCII
    literal, every observed index must be a constant, and an out-of-range
    index returns zero.  String storage itself remains opaque; aliases,
    dynamic indices, nonliteral writes, and other observations stay loud.
    """
    try:
        if type(expression).__name__ != "ElementSelectExpression":
            return None
        receiver = expression.value
        if (type(receiver).__name__ != "NamedValueExpression"
                or type(receiver.type.canonicalType).__name__ != "StringType"):
            return None
        index = _literal_integral_value(expression.selector)
        if index is None:
            return None
        symbol = receiver.symbol
        initializer = getattr(symbol, "initializer", None)
        while type(initializer).__name__ == "ConversionExpression":
            initializer = getattr(initializer, "operand", None)
        initial_value = (getattr(initializer, "value", None)
                         if type(initializer).__name__ == "StringLiteral"
                         and not getattr(initializer, "bad", False) else None)
        if (initial_value is not None
                and (not isinstance(initial_value, str)
                     or any(ord(char) == 0 or ord(char) > 127
                            for char in initial_value))):
            return None
        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        assignments = []
        dynamic_index = False
        invalid_write = False
        if instance is not None:
            def inspect(node):
                nonlocal dynamic_index, invalid_write
                kind = type(node).__name__
                if kind == "ElementSelectExpression":
                    value = getattr(node, "value", None)
                    if (type(value).__name__ == "NamedValueExpression"
                            and getattr(value, "symbol", None) is symbol
                            and _literal_integral_value(node.selector) is None):
                        dynamic_index = True
                    return
                if kind != "AssignmentExpression":
                    return
                left = getattr(node, "left", None)
                if left is None:
                    return
                if (type(left).__name__ == "ElementSelectExpression"
                        and type(getattr(left, "value", None)).__name__
                        == "NamedValueExpression"
                        and getattr(left.value, "symbol", None) is symbol):
                    invalid_write = True
                    return
                if (getattr(left, "symbol", None) is not symbol):
                    return
                if (getattr(node, "op", None) is not None
                        or getattr(node, "timingControl", None) is not None
                        or getattr(node, "isNonBlocking", False)):
                    invalid_write = True
                    return
                value = node.right
                while type(value).__name__ == "ConversionExpression":
                    value = getattr(value, "operand", None)
                if (type(value).__name__ != "StringLiteral"
                        or getattr(value, "bad", False)
                        or not isinstance(getattr(value, "value", None), str)
                        or any(ord(char) == 0 or ord(char) > 127
                               for char in value.value)):
                    invalid_write = True
                    return
                assignments.append((getattr(node.sourceRange.start, "offset", -1),
                                    value.value))
            instance.visit(inspect)
        if dynamic_index or invalid_write:
            return None
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        code_source = _sv_code_source(source)
        occurrences = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", code_source))
        if not occurrences:
            return None
        for match in occurrences[1:]:
            tail = source[match.end():].lstrip()
            if tail.startswith("[") or re.match(r'=\s*"', tail):
                continue
            return None
        position = getattr(getattr(expression, "sourceRange", None), "start", None)
        position = getattr(position, "offset", None)
        if position is None:
            return None
        history = [(start, value) for start, value in assignments if start < position]
        if initial_value is not None:
            history.insert(0, (-1, initial_value))
        if not history:
            return None
        value = max(history, key=lambda item: item[0])[1]
        return ord(value[index]) if 0 <= index < len(value) else 0
    except Exception:
        return None


def _convert_string_literal_getc(sm, expression):
    if not _string_literal_getc_method(expression):
        return unsupported(sm, expression, "CallExpression:string-getc")
    value = _string_literal_source_value(expression, "getc")
    if value is None:
        return unsupported(sm, expression, "CallExpression:string-getc")
    index = _literal_integral_value(expression.arguments[1])
    byte = ord(value[index]) if 0 <= index < len(value) else 0
    width = expression.type.bitWidth
    return signed_metadata({
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": width,
        "bits": format(byte & ((1 << width) - 1), f"0{width}b"),
        "string_literal_getc_query": True,
    }, expression.type)


def _string_literal_len_method(expression):
    """Recognize ``len`` on a string whose value is a pure literal.

    The flat state has no string slot, but the length of an unchanged literal
    is a scalar fact that can be lowered exactly.  Keep this separate from
    the zero-length rule: nonempty literal contents are not otherwise exposed
    by the self-check state, and every write or other string operation stays
    loud.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "len"):
            return False
        arguments = list(expression.arguments)
        if len(arguments) != 1 or type(arguments[0]).__name__ != "NamedValueExpression":
            return False
        receiver = arguments[0]
        if type(receiver.type.canonicalType).__name__ != "StringType":
            return False
        symbol = receiver.symbol
        initializer = getattr(symbol, "initializer", None)
        while type(initializer).__name__ == "ConversionExpression":
            initializer = getattr(initializer, "operand", None)
        initial_value = (getattr(initializer, "value", None)
                         if type(initializer).__name__ == "StringLiteral"
                         and not getattr(initializer, "bad", False) else None)
        if (initial_value is not None and
                (not isinstance(initial_value, str)
                 or any(ord(char) == 0 or ord(char) > 127 for char in initial_value))):
            return False
        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        assignments = []
        if instance is not None:
            def inspect(node):
                if (type(node).__name__ != "AssignmentExpression"
                        or getattr(node, "left", None) is None
                        or getattr(node.left, "symbol", None) is not symbol
                        or getattr(node, "op", None) is not None
                        or getattr(node, "timingControl", None) is not None):
                    return
                value = node.right
                while type(value).__name__ == "ConversionExpression":
                    value = getattr(value, "operand", None)
                if (type(value).__name__ != "StringLiteral"
                        or getattr(value, "bad", False)
                        or not isinstance(getattr(value, "value", None), str)
                        or any(ord(char) == 0 or ord(char) > 127
                               for char in value.value)):
                    return
                assignments.append((getattr(node.left.sourceRange.start, "offset", -1),
                                    getattr(value, "value", "")))
            instance.visit(inspect)
        name = getattr(receiver.symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        # Discover runtime occurrences in code only.  Comments and diagnostic
        # strings can mention the receiver without being another observation;
        # keep the raw source for the suffix spelling and source offsets below.
        code_source = _sv_code_source(source)
        occurrences = list(re.finditer(r"(?<![A-Za-z0-9_$])" + re.escape(name)
                                       + r"(?![A-Za-z0-9_$])", code_source))
        if not occurrences:
            return False
        def inert_occurrence(match):
            tail = source[match.end():].lstrip()
            if tail.startswith(".len"):
                return True
            # ``len`` and ``getc`` are both scalar observations of the same
            # proven literal.  A source may use either query (the conformance
            # tests intentionally combine them), so neither makes the other
            # history recognizer unsafe.
            if tail.startswith(".getc"):
                return True
            if tail.startswith("="):
                # The source spelling must be a literal assignment.  AST
                # offsets include trivia differently from the raw source
                # buffer.  A predefined string macro is nevertheless a
                # StringLiteral in the AST, so accept it by matching the
                # occurrence to the collected literal assignment offset.
                if re.match(r'=\s*"', tail) is not None:
                    return True
                return any(start >= 0 and abs(start - match.start()) <= 8
                           for start, _ in assignments)
            return False
        if not all(inert_occurrence(match) for match in occurrences[1:]):
            return False
        position = getattr(getattr(expression, "sourceRange", None), "start", None)
        position = getattr(position, "offset", None)
        if position is None:
            return False
        history = [(start, value) for start, value in assignments if start < position]
        if initial_value is not None:
            history.insert(0, (-1, initial_value))
        return bool(history)
    except Exception:
        return False


def _string_literal_source_value(expression, method, receiver=None,
                                 permit_argument=None):
    """Return the latest ASCII literal assigned to a string receiver."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != method):
            return None
        arguments = list(expression.arguments)
        if receiver is None:
            if not arguments:
                return None
            receiver = arguments[0]
        if type(receiver.type.canonicalType).__name__ != "StringType":
            return None
        symbol = receiver.symbol
        initializer = getattr(symbol, "initializer", None)
        while type(initializer).__name__ == "ConversionExpression":
            initializer = getattr(initializer, "operand", None)
        initial_value = (getattr(initializer, "value", None)
                         if type(initializer).__name__ == "StringLiteral"
                         and not getattr(initializer, "bad", False) else None)
        if (initial_value is not None and
                (not isinstance(initial_value, str)
                 or any(ord(char) == 0 or ord(char) > 127 for char in initial_value))):
            return None
        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        assignments = []
        if instance is not None:
            def inspect(node):
                if (type(node).__name__ != "AssignmentExpression"
                        or getattr(node, "left", None) is None
                        or getattr(node.left, "symbol", None) is not symbol
                        or getattr(node, "op", None) is not None
                        or getattr(node, "timingControl", None) is not None):
                    return
                value = node.right
                while type(value).__name__ == "ConversionExpression":
                    value = getattr(value, "operand", None)
                if (type(value).__name__ != "StringLiteral"
                        or getattr(value, "bad", False)
                        or not isinstance(getattr(value, "value", None), str)
                        or any(ord(char) == 0 or ord(char) > 127
                               for char in value.value)):
                    return
                assignments.append((getattr(node.sourceRange.start, "offset", -1),
                                    value.value))
            instance.visit(inspect)
        name = getattr(symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        # Mask comments and string contents before locating source-order
        # references.  The original source remains authoritative for suffix
        # spelling and offset-based assignment ordering.
        code_source = _sv_code_source(source)
        occurrences = list(re.finditer(
            r"(?<![A-Za-z0-9_$])" + re.escape(name)
            + r"(?![A-Za-z0-9_$])", code_source))
        if not occurrences:
            return None
        for match in occurrences[1:]:
            tail = source[match.end():].lstrip()
            if (tail.startswith("." + method)
                    or (method in ("len", "getc")
                        and tail.startswith((".len", ".getc")))
                    or (method in ("compare", "icompare")
                        and tail.startswith((".compare", ".icompare")))
                    or (method in ("toupper", "tolower", "substr")
                        and tail.startswith((".toupper", ".tolower", ".substr")))
                    or re.match(r'=\s*"', tail)):
                continue
            if (permit_argument is not None
                    and type(permit_argument).__name__ == "NamedValueExpression"
                    and abs(match.start()
                            - getattr(permit_argument.sourceRange.start,
                                      "offset", -100000)) <= 8):
                continue
            method_pattern = (r'(?:compare|icompare)'
                              if method in ("compare", "icompare")
                              else re.escape(method))
            if re.search(r'\.' + method_pattern
                         + r'\s*\([^;]*$', source[:match.start()]):
                continue
            return None
        position = getattr(getattr(expression, "sourceRange", None), "start", None)
        position = getattr(position, "offset", None)
        if position is None:
            return None
        history = [(start, value) for start, value in assignments if start < position]
        if initial_value is not None:
            history.insert(0, (-1, initial_value))
        return max(history, key=lambda item: item[0])[1] if history else None
    except Exception:
        return None


def _floating_string_atoreal_call(expression):
    """Whether ``string.atoreal()`` is a source-pure opaque real result.

    The legacy self-check state deliberately has no real-valued storage.  A
    blocking write of a conversion from a proven ASCII literal therefore has
    no represented effect, just like the existing literal and pure IEEE math
    writes.  Keep the receiver history check in one place with the other
    string methods; aliases, dynamic writes, and every other observation stay
    on the normal loud boundary.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName != "atoreal"):
            return False
        arguments = list(expression.arguments)
        if len(arguments) != 1:
            return False
        receiver = arguments[0]
        if type(receiver).__name__ != "NamedValueExpression":
            return False
        if type(receiver.type.canonicalType).__name__ != "StringType":
            return False
        return _string_literal_source_value(expression, "atoreal") is not None
    except Exception:
        return False


def _string_literal_atoi_method(expression):
    """Recognize ``atoi`` on a source-pure ASCII string literal."""
    return _string_literal_source_value(expression, "atoi") is not None


_STRING_RADIX_METHODS = {"atobin": 1, "atooct": 3, "atohex": 4}


def _string_literal_radix_method(expression):
    """Recognize a literal string radix conversion with scalar output."""
    try:
        method = getattr(expression, "subroutineName", None)
        if method not in _STRING_RADIX_METHODS:
            return False
        value = _string_literal_source_value(expression, method)
        width = getattr(expression.type, "bitWidth", None)
        return (value is not None and width == 32
                and getattr(expression.type, "isIntegral", False))
    except Exception:
        return False


def _convert_string_literal_radix(sm, expression):
    if not _string_literal_radix_method(expression):
        return unsupported(sm, expression, "CallExpression:string-radix")
    method = expression.subroutineName
    value = _string_literal_source_value(expression, method)
    group = _STRING_RADIX_METHODS[method]
    digits = "0123456789abcdef"
    bits = []
    for char in value.lower():
        if char in "?":
            char = "z"
        if char in "xz":
            bits.append(char * group)
            continue
        if char not in digits:
            return unsupported(sm, expression, "CallExpression:string-radix-digit")
        number = digits.index(char)
        if number >= (1 << group):
            return unsupported(sm, expression, "CallExpression:string-radix-digit")
        bits.append(format(number, f"0{group}b"))
    encoded = "".join(bits)
    if len(encoded) > 32:
        encoded = encoded[-32:]
    encoded = encoded.rjust(32, "0")
    return signed_metadata({
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": 32,
        "bits": encoded,
        "string_literal_radix": method,
    }, expression.type)


def _convert_string_literal_atoi(sm, expression):
    value = _string_literal_source_value(expression, "atoi")
    if value is None:
        return unsupported(sm, expression, "CallExpression:string-atoi")
    digits = []
    for char in value:
        if "0" <= char <= "9":
            digits.append(char)
        elif char == "_" and digits:
            continue
        else:
            break
    parsed = int("".join(digits), 10) if digits else 0
    width = getattr(expression.type, "bitWidth", None)
    if (width != 32 or not getattr(expression.type, "isIntegral", False)
            or not getattr(expression.type, "isSigned", False)
            or parsed >= (1 << (width - 1))):
        return unsupported(sm, expression, "CallExpression:string-atoi-range")
    return signed_metadata({
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": width,
        "bits": format(parsed, f"0{width}b"),
        "string_literal_atoi": True,
    }, expression.type)


def _string_literal_compare_method(expression):
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName not in ("compare", "icompare")
                or len(expression.arguments) != 2):
            return False
        left = _string_literal_source_value(
            expression, expression.subroutineName,
            permit_argument=expression.arguments[0])
        right = expression.arguments[1]
        node = right
        while type(node).__name__ == "ConversionExpression":
            node = getattr(node, "operand", None)
        if type(node).__name__ == "StringLiteral":
            value = getattr(node, "value", None)
            right_value = (value if isinstance(value, str)
                           and all(ord(char) != 0 and ord(char) <= 127
                                    for char in value) else None)
        else:
            right_value = _string_literal_source_value(
                expression, expression.subroutineName,
                receiver=right, permit_argument=right)
        return left is not None and right_value is not None
    except Exception:
        return False


def _convert_string_literal_compare(sm, expression):
    if not _string_literal_compare_method(expression):
        return unsupported(sm, expression, "CallExpression:string-compare")
    method = expression.subroutineName
    left = _string_literal_source_value(
        expression, method, permit_argument=expression.arguments[0])
    right = expression.arguments[1]
    node = right
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
    if type(node).__name__ == "StringLiteral":
        right_value = node.value
    else:
        right_value = _string_literal_source_value(
            expression, method, receiver=right, permit_argument=right)
    if method == "icompare":
        left, right_value = left.lower(), right_value.lower()
    result = -1 if left < right_value else (1 if left > right_value else 0)
    width = getattr(expression.type, "bitWidth", None)
    if width != 32 or not getattr(expression.type, "isSigned", False):
        return unsupported(sm, expression, "CallExpression:string-compare-width")
    return signed_metadata({
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": width,
        "bits": format(result & ((1 << width) - 1), f"0{width}b"),
        "string_literal_icompare" if method == "icompare"
        else "string_literal_compare": True,
    }, expression.type)


def _convert_string_literal_len_method(sm, expression):
    if not _string_literal_len_method(expression):
        return unsupported(sm, expression, "CallExpression:string-len")
    receiver = expression.arguments[0]
    symbol = receiver.symbol
    initializer = getattr(symbol, "initializer", None)
    while type(initializer).__name__ == "ConversionExpression":
        initializer = initializer.operand
    value = (initializer.value if type(initializer).__name__ == "StringLiteral"
             else "")
    instance = getattr(getattr(symbol, "parentScope", None),
                       "containingInstance", None)
    position = expression.sourceRange.start.offset
    if instance is not None:
        def inspect(node):
            nonlocal value
            if (type(node).__name__ != "AssignmentExpression"
                    or getattr(node, "left", None) is None
                    or getattr(node.left, "symbol", None) is not symbol
                    or getattr(node, "op", None) is not None
                    or getattr(node, "timingControl", None) is not None
                    or node.sourceRange.start.offset >= position):
                return
            candidate = node.right
            while type(candidate).__name__ == "ConversionExpression":
                candidate = getattr(candidate, "operand", None)
            if type(candidate).__name__ == "StringLiteral":
                value = candidate.value
        instance.visit(inspect)
    return {
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": expression.type.bitWidth,
        "bits": format(len(value) & ((1 << expression.type.bitWidth) - 1),
                        f"0{expression.type.bitWidth}b"),
        "string_literal_length_query": True,
    }


def _convert_zero_size_method(sm, expression):
    if not _zero_size_method(expression):
        return unsupported(sm, expression, "CallExpression:size")
    return {
        "kind": "Literal",
        "span": node_span(sm, expression),
        "width": expression.type.bitWidth,
        "bits": "0" * expression.type.bitWidth,
        ("zero_size_query" if expression.subroutineName == "size"
         else "zero_string_length_query"): True,
    }


def _new_integer_arg(expr, value, implicit):
    """Whether a class construction has one literal integer constructor arg."""
    node = expr
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return False
    if type(node).__name__ != "NewClassExpression" or getattr(node, "bad", False):
        return False
    call = getattr(node, "constructorCall", None)
    if type(call).__name__ != "CallExpression":
        return False
    try:
        args = list(call.arguments)
    except Exception:
        return False
    if len(args) != 1:
        return False
    arg = args[0]
    return (type(arg).__name__ == "IntegerLiteral"
            and getattr(arg, "value", None) == value
            and (getattr(arg, "syntax", None) is None) == implicit
            and not getattr(arg, "bad", False))


def _bare_new(expr):
    """Whether a class construction spells exactly ``new()``."""
    return _new_integer_arg(expr, 0, True)


def _explicit_new_zero(expr):
    """Whether a class construction spells exactly ``new(0)``."""
    return _new_integer_arg(expr, 0, False)


def _semaphore_new_nonnegative_literal(expr):
    """Whether ``new(N)`` constructs a semaphore with a known N >= 0."""
    try:
        node = expr
        while type(node).__name__ == "ConversionExpression":
            node = getattr(node, "operand", None)
            if node is None:
                return False
        if type(node).__name__ != "NewClassExpression" or getattr(node, "bad", False):
            return False
        call = getattr(node, "constructorCall", None)
        args = list(getattr(call, "arguments", []))
        if not args:
            return True
        if len(args) != 1:
            return False
        value = _literal_integral_value(args[0])
        return value is not None and value >= 0
    except Exception:
        return False


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


def _invalid_associative_index_target(lhs):
    """Whether an associative-array element selection violates §7.8.4/5."""
    try:
        if type(lhs).__name__ != "ElementSelectExpression":
            return False
        array_type = lhs.value.type.canonicalType
        if type(array_type).__name__ != "AssociativeArrayType":
            return False
        index_type = array_type.indexType.canonicalType
        selector = lhs.selector
        selector_type = selector.type.canonicalType
        index_kind = type(index_type).__name__
        selector_kind = type(selector_type).__name__
        if type(selector).__name__ == "ConversionExpression":
            operand = getattr(selector, "operand", None)
            operand_type = getattr(operand, "type", None)
            operand_canonical = getattr(operand_type, "canonicalType",
                                        operand_type)
            selector_kind = type(operand_canonical).__name__
        # Floating-point associative keys are forbidden, and a real/shortreal
        # selector may not be implicitly converted to an integral key.
        return (index_kind == "FloatingType"
                or selector_kind == "FloatingType")
    except Exception:
        return False


def _invalid_struct_replication_assignment(expression):
    """Whether a structure assignment pattern illegally uses replication."""
    try:
        if type(expression.right).__name__ != "ReplicatedAssignmentPatternExpression":
            return False
        target_type = expression.left.type.canonicalType
        return type(target_type).__name__ in ("UnpackedStructType", "PackedStructType")
    except Exception:
        return False


def _invalid_string_unknown_replication(expression):
    """Whether a string replication multiplier is a known x/z value."""
    try:
        right = expression.right
        if (type(right).__name__ != "ReplicationExpression"
                or type(expression.left.type.canonicalType).__name__ != "StringType"):
            return False
        count = right.count
        initializer = getattr(getattr(count, "symbol", None), "initializer", None)
        if type(initializer).__name__ == "IntegerLiteral":
            bits = str(initializer.value)
            return any(bit in bits.lower() for bit in ("x", "z"))
        if type(count).__name__ == "IntegerLiteral":
            bits = str(count.value)
            return any(bit in bits.lower() for bit in ("x", "z"))
        return False
    except Exception:
        return False


def legacy_blocking_target(sm, lhs, concat_leaf=False):
    expression_kind = type(lhs).__name__
    if expression_kind == "ElementSelectExpression":
        assoc_cell = _finite_string_assoc_cell(sm, lhs)
        if assoc_cell is not None:
            target = {
                "kind": "Ident",
                "span": node_span(sm, lhs),
                "width": assoc_cell["width"],
                "name": assoc_cell["name"],
            }
            if concat_leaf:
                target["two_state"] = assoc_cell["two_state"]
            return target, True
        assoc_cell = _finite_integral_assoc_cell(sm, lhs)
        if assoc_cell is not None:
            target = {
                "kind": "Ident",
                "span": node_span(sm, lhs),
                "width": assoc_cell["width"],
                "name": assoc_cell["name"],
            }
            if concat_leaf:
                target["two_state"] = assoc_cell["two_state"]
            return target, True
    if expression_kind in ("ElementSelectExpression", "RangeSelectExpression"):
        nested_window = _nested_packed_constant_window(
            sm, lhs, "SelectTarget")
        if nested_window is not None:
            return nested_window, True
        packed_array_window = _fixed_array_packed_window(
            sm, lhs, "SelectTarget")
        if packed_array_window is not None:
            return packed_array_window, True
        dynamic_packed_array_window = _fixed_array_dynamic_packed_window(
            sm, lhs, "SelectTarget")
        if dynamic_packed_array_window is not None:
            return dynamic_packed_array_window, True
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
            and _constant_dimension_selector(index) is not None):
        # Generate elaboration binds genvar arithmetic to a constant, but
        # slang keeps the original expression tree on the selected target.
        # Continuous-driver window accounting needs the resulting fixed bit
        # offset, so normalize every bound constant packed label here (the
        # non-canonical range case also needs its declared-label conversion).
        normalized = _packed_constant_index(sm, lhs.value.type, index)
        if normalized is None:
            return unsupported(sm, lhs, expression_kind + ":target-source"), False
        converted_index, index_signed = normalized
    elif (expression_kind == "ElementSelectExpression"
          and canonical_kind == "PackedArrayType"
          and not canonical_select):
        # Reuse the read-side label normalizer for pure signed dynamic
        # element targets.  It preserves the older 32-bit signed boundary for
        # one-bit elements and scales wide nested elements by their width.
        normalized = _packed_element_index(sm, lhs.value.type, index)
        if normalized is None:
            return unsupported(sm, lhs, expression_kind + ":target-source"), False
        converted_index, index_signed = normalized
    elif (expression_kind == "RangeSelectExpression"
          and canonical_kind == "PackedArrayType"
          and _constant_dimension_selector(index) is not None
          and str(lhs.selectionKind).split(".")[-1] in ("IndexedUp", "IndexedDown")):
        # Generate elaboration binds a genvar-based indexed part-select to a
        # constant label, but slang retains the arithmetic expression on the
        # selected target. Normalize that label to the flat vector offset.
        normalized = _packed_constant_indexed_index(
            sm, lhs.value.type, index, lhs.type.bitWidth,
            str(lhs.selectionKind).split(".")[-1] == "IndexedDown")
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
            dynamic = _packed_dynamic_indexed_index(
                sm, lhs.value.type, index, lhs.type.bitWidth, selection)
            if dynamic is None:
                normalized = None
            else:
                converted_index, index_signed, descending = dynamic
                normalized = (converted_index, index_signed, descending)
        else:
            normalized = None
        if normalized is None:
            return unsupported(sm, lhs, expression_kind + ":target-source"), False
        if len(normalized) == 3:
            converted_index, index_signed, descending = normalized
        else:
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


def _streaming_slice_size(lhs):
    """Resolve an explicit streaming slice size, including named types.

    Slang exposes a numeric slice directly for ``{>>8{...}}`` but leaves a
    named integral type such as ``byte`` at zero on the elaborated node.  The
    syntax kind still carries the standard type width; keep this resolver
    deliberately limited to the fixed built-in integral spellings used by
    the target lowering.
    """
    try:
        value = getattr(lhs, "sliceSize", None)
        if isinstance(value, int) and value > 0:
            return value
        syntax = getattr(lhs, "syntax", None)
        token = getattr(syntax, "sliceSize", None)
        kind = str(getattr(token, "kind", "")).split(".")[-1]
        if kind == "IntegerLiteralExpression":
            text = getattr(getattr(token, "literal", None), "valueText", None)
            if text is not None and str(text).isdigit():
                value = int(text)
                return value if value > 0 else None
        return {
            "ByteType": 8,
            "ShortIntType": 16,
            "IntType": 32,
            "IntegerType": 32,
            "LongIntType": 64,
            "TimeType": 64,
        }.get(kind)
    except Exception:
        return None


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


def _fixed_array_stream_targets(sm, operand, symbolic=False):
    """Expand a complete fixed unpacked array into its flattened cells.

    The storage tier represents every constant leaf of a bounded unpacked
    array by an ordinary vector name.  A right-streaming unpack of the whole
    array therefore has the same target geometry as an explicit list of
    element selects: dimensions and indices are visited in declaration order
    (the leftmost dimension is the outer loop).  Partial selections, dynamic
    indices, and non-integral leaves deliberately return ``None`` so their
    existing loud boundary remains in force.
    """
    try:
        if not _storage_expression(operand):
            return None
        if str(operand.symbol.kind) not in ("SymbolKind.Variable", "SymbolKind.Net"):
            return None
        shape = _fixed_array_dimensions(operand.type)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        width, two_state, reason = type_width_2s(leaf_type)
        if width is None or reason is not None:
            return None
        positions = [()]
        for left, right in dimensions:
            step = 1 if right >= left else -1
            positions = [prefix + (position,)
                         for prefix in positions
                         for position in range(left, right + step, step)]
        base = (_storage_name(operand.symbol) if symbolic
                else _array_storage_name(operand.symbol))
        return [{
            "kind": "Ident",
            "span": node_span(sm, operand),
            "width": width,
            "name": base + "".join(f"[{position}]" for position in indexes),
            "two_state": two_state,
        } for indexes in positions]
    except Exception:
        return None


def _streaming_struct_source(sm, operand):
    """Flatten one unpacked integral struct operand in declaration order."""
    try:
        path = _unpacked_struct_path(operand)
        if path is None:
            return None
        base, aggregate = path
        if type(aggregate).__name__ != "UnpackedStructType":
            return None
        cells = _unpacked_struct_field_cells(base, aggregate,
                                              node_span(sm, operand))
        if not cells:
            return None
        parts = [{"kind": "Ident", "span": node_span(sm, operand),
                  "width": width, "name": name}
                 for name, width, _init, _type in cells]
        return {"kind": "Concat", "span": node_span(sm, operand),
                "width": sum(part["width"] for part in parts),
                "parts": parts}
    except Exception:
        return None


def _fixed_array_stream_targets_with(sm, operand, with_expr, symbolic=False):
    """Expand a constant ``with`` range of a fixed unpacked array.

    Both the ordinary ``[left:right]`` spelling and the indexed part-range
    spellings ``[base +: width]``/``[base -: width]`` are statically bounded
    here.  The resulting list is the source-order list of selected cells; the
    surrounding streaming lowering still samples one RHS and leaves every
    unselected cell untouched.  Dynamic bounds and partial aggregate paths
    remain outside the flat cell representation.
    """
    try:
        if type(with_expr).__name__ != "RangeSelectExpression":
            return None
        selection = str(with_expr.selectionKind).split(".")[-1]
        if selection not in ("Simple", "IndexedUp", "IndexedDown"):
            return None
        base = _constant_dimension_selector(with_expr.left)
        extent = _constant_dimension_selector(with_expr.right)
        if base is None or extent is None:
            return None
        shape = _fixed_array_shape(operand)
        if shape is None:
            return None
        _name, _width, _two_state, array_left, array_right = shape
        # Keep the cell order identical to the dynamic-array streaming
        # contract.  A descending fixed dimension has a separate declaration
        # order and remains loud until that ordering is represented explicitly.
        if array_left > array_right:
            return None
        lo, hi = min(array_left, array_right), max(array_left, array_right)
        if selection == "Simple":
            if (base < lo or base > hi or extent < lo or extent > hi
                    or base > extent):
                return None
            selected_positions = list(range(base, extent + 1))
        else:
            if extent <= 0:
                return None
            if selection == "IndexedUp":
                selected_positions = list(range(base, base + extent))
            else:
                selected_positions = list(range(base - extent + 1, base + 1))
            if any(position < lo or position > hi
                   for position in selected_positions):
                return None
        targets = _fixed_array_stream_targets(sm, operand, symbolic)
        if targets is None:
            return None
        by_position = {}
        step = 1 if array_right >= array_left else -1
        positions = list(range(array_left, array_right + step, step))
        if len(positions) != len(targets):
            return None
        by_position.update(zip(positions, targets))
        return [by_position[position] for position in selected_positions]
    except Exception:
        return None


def _dynamic_streaming_with_prefix_target_assignment(sm, expr):
    """Lower a stream whose extent names an earlier target in the same stream.

    IEEE evaluates a ``with`` expression immediately before its stream.  In
    ``{>> {len, payload with [0 +: len]}}`` the first target is therefore
    unpacked before the dynamic extent is read.  The flat self-check state can
    admit the narrow constant-source form by sampling that prefix value and
    expanding the corresponding dynamic-array cells.  Computed sources,
    aliases, multiple writes, and control-dependent writes stay loud.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None):
            return None
        lhs = expr.left
        if type(lhs).__name__ != "StreamingConcatenationExpression":
            return None
        token = getattr(getattr(lhs, "syntax", None), "operatorToken", None)
        if str(getattr(token, "kind", "")).split(".")[-1] != "RightShift":
            return None
        streams = list(lhs.streams)
        if len(streams) < 2:
            return None
        final = streams[-1]
        operand = getattr(final, "operand", None)
        with_expr = getattr(final, "withExpr", None)
        if (operand is None or type(with_expr).__name__ != "RangeSelectExpression"
                or str(with_expr.selectionKind).split(".")[-1] != "IndexedUp"
                or type(operand.type.canonicalType).__name__ != "DynamicArrayType"):
            return None
        base = _constant_dimension_selector(with_expr.left)
        extent_expr = with_expr.right
        if (base is None or type(extent_expr).__name__ != "NamedValueExpression"
                or getattr(extent_expr, "symbol", None) is None):
            return None
        extent_width, _extent_two, extent_reason = type_width_2s(extent_expr.type)
        if extent_width is None or extent_reason is not None:
            return None

        prefix_parts = []
        prefix_width = 0
        prefix_symbols = []
        for stream in streams[:-1]:
            if getattr(stream, "withExpr", None) is not None:
                return None
            prefix = getattr(stream, "operand", None)
            if type(prefix).__name__ != "NamedValueExpression":
                return None
            target, admitted = legacy_blocking_target(sm, prefix, True)
            if (not admitted or target is None
                    or target.get("kind") not in ("Ident", "SelectTarget")):
                return None
            width = width_of(target)
            if width is None or width <= 0:
                return None
            prefix_parts.append(target)
            prefix_width += width
            prefix_symbols.append(prefix.symbol)
        if extent_expr.symbol not in prefix_symbols:
            return None

        shape = _fixed_array_shape(operand)
        if shape is None:
            return None
        name, width, two_state, left, right = shape
        if left > right or base < left or base > right:
            return None
        targets = _fixed_array_stream_targets(sm, operand, False)
        if targets is None or len(targets) != right - left + 1:
            targets = [{
                "kind": "Ident", "span": node_span(sm, operand),
                "width": width, "name": f"{name}[{position}]",
                "two_state": two_state,
            } for position in range(left, right + 1)]

        # The source must have one earlier, unconditional assignment whose
        # converted value supplies the prefix and payload bits.  This keeps
        # the sampled extent independent of a live scheduler or alias.
        source = expr.right
        if type(source).__name__ != "NamedValueExpression":
            return None
        source_symbol = getattr(source, "symbol", None)
        if source_symbol is None:
            return None
        assignments = []
        controls = []

        def inspect(node):
            kind = type(node).__name__
            if kind == "AssignmentExpression":
                left_expr = getattr(node, "left", None)
                if (type(left_expr).__name__ == "NamedValueExpression"
                        and getattr(left_expr, "symbol", None) is source_symbol):
                    assignments.append(node)
            elif kind in ("ConditionalStatement", "ForLoopStatement",
                          "WhileLoopStatement", "DoWhileLoopStatement",
                          "RepeatLoopStatement", "ForeachLoopStatement",
                          "CaseStatement", "CaseInsideStatement",
                          "CasePatternStatement", "LoopStatement"):
                controls.append(node)

        source_symbol.parentScope.containingInstance.visit(inspect)
        if len(assignments) != 1:
            return None
        source_assignment = assignments[0]
        if (source_assignment.sourceRange.start.offset >= expr.sourceRange.start.offset
                or source_assignment.op is not None
                or source_assignment.isNonBlocking
                or source_assignment.timingControl is not None
                or any(control.sourceRange.start.offset <=
                       source_assignment.sourceRange.start.offset and
                       source_assignment.sourceRange.end.offset <=
                       control.sourceRange.end.offset for control in controls)):
            return None
        value = convert_expr(sm, source_assignment.right)
        if (value is None or value.get("kind") == "Unsupported"
                or not _case_source_expression_ok(source_assignment.right)
                or width_of(value) is None or not _case_expression_ok(value)):
            return None
        source_width = width_of(value)

        def static_bits(node):
            if not isinstance(node, dict):
                return None
            kind = node.get("kind")
            if kind == "Squash2":
                return static_bits(node.get("operand"))
            if kind == "Literal":
                bits = node.get("bits")
                return bits if isinstance(bits, str) and all(
                    bit in "01" for bit in bits) else None
            if kind == "Concat":
                pieces = [static_bits(part) for part in node.get("parts", [])]
                return "".join(pieces) if pieces and all(
                    piece is not None for piece in pieces) else None
            return None

        bits = static_bits(value)
        if bits is None or len(bits) != source_width or prefix_width > len(bits):
            return None
        prefix_value = bits[:prefix_width]
        if any(bit not in "01" for bit in prefix_value):
            return None
        extent_value = int(prefix_value, 2)
        if extent_value < 0 or extent_value > right - base + 1:
            return None
        if extent_value == 0:
            return {"kind": "Empty", "span": node_span(sm, expr),
                    "dynamic_stream_with_prefix_zero_extent": True}
        total_width = prefix_width + extent_value * width
        if total_width > source_width:
            return None
        selected = targets[base - left:base - left + extent_value]
        if len(selected) != extent_value:
            return None
        target = {"kind": "ConcatTarget", "span": node_span(sm, lhs),
                  "width": total_width,
                  "parts": prefix_parts + [dict(t) for t in selected]}
        return {
            "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
            "span": node_span(sm, expr), "target": target,
            "value": _streaming_source_window(convert_expr(sm, source),
                                                total_width, False),
            "dynamic_stream_with_prefix_lowered": True,
        }
    except Exception:
        return None


def _dynamic_streaming_with_target_assignment(sm, expr):
    """Lower a finite dynamic-array stream with a runtime ``with`` extent.

    A dynamic array whose one allocation has a constant extent is already
    represented by independent flat cells.  The remaining target-only shape
    in this family is ``{>> {a with [base +: count]}}`` where ``count`` is an
    ordinary integral variable with one unconditional literal assignment
    before the stream.  That assignment is sampled exactly once by the
    source statement, so the existing stream-window lowering can emit the
    corresponding finite target directly.  Control-dependent, multiply
    assigned, out-of-range, or effectful extents remain loud.

    Keep this rung deliberately narrow: one ascending dynamic-array stream,
    a constant base, and a single integral extent expression.  Multi-stream
    aggregates, dynamic bases, descending arrays, and effectful RHSs still
    use the ordinary target boundary.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None):
            return None
        lhs = expr.left
        if type(lhs).__name__ != "StreamingConcatenationExpression":
            return None
        token = getattr(getattr(lhs, "syntax", None), "operatorToken", None)
        if str(getattr(token, "kind", "")).split(".")[-1] != "RightShift":
            return None
        if len(lhs.streams) != 1:
            return _dynamic_streaming_with_prefix_target_assignment(sm, expr)
        stream = lhs.streams[0]
        operand = getattr(stream, "operand", None)
        with_expr = getattr(stream, "withExpr", None)
        if (operand is None or type(with_expr).__name__ != "RangeSelectExpression"
                or str(with_expr.selectionKind).split(".")[-1] != "IndexedUp"):
            return None
        # The left bound is a dimension index, while the right bound is the
        # run-time extent.  The ordinary constant helper already rejects
        # unsized/unknown values and gives us the elaborated array index.
        base = _constant_dimension_selector(with_expr.left)
        if base is None:
            return None
        extent_expr = with_expr.right
        extent_width, _extent_two, extent_reason = type_width_2s(extent_expr.type)
        if extent_width is None or extent_reason is not None:
            return None
        if (type(extent_expr).__name__ != "NamedValueExpression"
                and not _case_source_expression_ok(extent_expr)):
            return None
        shape = _fixed_array_shape(operand)
        if shape is None:
            return None
        name, width, two_state, left, right = shape
        if (type(operand.type.canonicalType).__name__ != "DynamicArrayType"
                or left > right or base < left or base > right):
            return None
        targets = _fixed_array_stream_targets(sm, operand, False)
        if targets is None or len(targets) != right - left + 1:
            # ``_fixed_array_stream_targets`` intentionally focuses on fixed
            # dimensions; build the already-sampled dynamic cells directly.
            targets = [{
                "kind": "Ident", "span": node_span(sm, operand),
                "width": width,
                "name": f"{name}[{position}]",
                "two_state": two_state,
            } for position in range(left, right + 1)]
        value = _convert_streaming_source(sm, expr.right)
        source_lowered = value is not None
        if value is None:
            value = convert_expr(sm, expr.right)
        if (value is None or value.get("kind") == "Unsupported"
                or (not source_lowered
                    and not _case_source_expression_ok(expr.right))
                or width_of(value) is None or not _case_expression_ok(value)):
            return None
        source_width = width_of(value)
        extent = convert_expr(sm, extent_expr)
        if (extent is None or extent.get("kind") == "Unsupported"
                or width_of(extent) != extent_width
                or not _case_expression_ok(extent)):
            return None
        # The flat envelope has no dynamic target node.  Admit the exact
        # source shape used by the corpus when the extent variable has one
        # unconditional literal assignment before this stream.  A control
        # dependent or multiply assigned extent remains the ordinary loud
        # target boundary rather than being guessed from source order.
        extent_value = None
        try:
            symbol = extent_expr.symbol
            instance = symbol.parentScope.containingInstance
            assignments = []
            controls = []

            def inspect(node):
                kind = type(node).__name__
                if kind == "AssignmentExpression":
                    left = getattr(node, "left", None)
                    if (type(left).__name__ == "NamedValueExpression"
                            and getattr(left, "symbol", None) is symbol):
                        assignments.append(node)
                elif kind in ("ConditionalStatement", "ForLoopStatement",
                              "WhileLoopStatement", "DoWhileLoopStatement",
                              "RepeatLoopStatement", "ForeachLoopStatement",
                              "CaseStatement", "CaseInsideStatement",
                              "CasePatternStatement", "LoopStatement"):
                    controls.append(node)

            instance.visit(inspect)
            if (getattr(symbol, "initializer", None) is None
                    and len(assignments) == 1):
                assignment = assignments[0]
                ar = assignment.sourceRange
                er = expr.sourceRange
                before = ar.start.offset < er.start.offset
                enclosed = any(
                    control.sourceRange.start.offset <= ar.start.offset
                    and ar.end.offset <= control.sourceRange.end.offset
                    for control in controls)
                if (before and not enclosed and assignment.op is None
                        and not assignment.isNonBlocking
                        and assignment.timingControl is None):
                    extent_value = _constant_dimension_selector(assignment.right)
        except Exception:
            extent_value = None
        if extent_value is None or extent_value < 0:
            return None
        count = int(extent_value)
        if count == 0:
            return {"kind": "Empty", "span": node_span(sm, expr),
                    "dynamic_stream_with_zero_extent": True}
        total_width = count * width
        if (count > right - base + 1 or total_width > source_width
                or count <= 0):
            return None
        selected = targets[base - left:base - left + count]
        if len(selected) != count:
            return None
        target = {"kind": "ConcatTarget", "span": node_span(sm, lhs),
                  "width": total_width, "parts": [dict(t) for t in selected]}
        return {
            "kind": "NonblockingAssign" if expr.isNonBlocking
            else "BlockingAssign",
            "span": node_span(sm, expr), "target": target,
            "value": _streaming_source_window(value, total_width, False),
            "dynamic_stream_with_lowered": True,
        }
    except Exception:
        return None


def _convert_streaming_source(sm, expression):
    """Convert a simple right-streaming source, including unpacked structs."""
    try:
        if type(expression).__name__ != "StreamingConcatenationExpression":
            return None
        token = getattr(getattr(expression, "syntax", None), "operatorToken", None)
        if str(getattr(token, "kind", "")).split(".")[-1] != "RightShift":
            return None
        if _streaming_has_slice_size(expression):
            return None
        parts = []
        for stream in expression.streams:
            operand = getattr(stream, "operand", None)
            if operand is None or getattr(stream, "withExpr", None) is not None:
                return None
            part = _streaming_struct_source(sm, operand)
            if part is None:
                width, _two_state, reason = type_width_2s(operand.type)
                if width is None or reason is not None or not _case_source_expression_ok(operand):
                    return None
                part = convert_expr(sm, operand)
                if (part is None or width_of(part) != width
                        or not _case_expression_ok(part)):
                    return None
            parts.append(part)
        if not parts:
            return None
        width = sum(width_of(part) for part in parts)
        if width != expression.bitstreamWidth:
            return None
        return {"kind": "Concat", "span": node_span(sm, expression),
                "width": width, "parts": parts}
    except Exception:
        return None


def _streaming_left_target_assignment(sm, expr, symbolic=False):
    """Lower a left stream over direct integral leaves.

    Left streaming reverses fixed-size chunks: the first target leaf receives
    the source's least-significant chunk, then the next chunk, and so on.  The
    admitted shape requires exact source and target widths and one target leaf
    per chunk. An omitted slice size is admitted only when every target leaf
    is one bit, matching the IEEE default. This keeps the lowering a pure
    sampled vector operation while leaving wider unsized, partial, dynamic,
    nested, and aggregate forms loud.
    """
    try:
        if (type(expr).__name__ != "AssignmentExpression" or expr.op is not None
                or expr.timingControl is not None
                or (symbolic and expr.isNonBlocking)):
            return None
        lhs = expr.left
        if type(lhs).__name__ != "StreamingConcatenationExpression":
            return None
        token = getattr(getattr(lhs, "syntax", None), "operatorToken", None)
        operator = str(getattr(token, "kind", "")).split(".")[-1]
        syntax = getattr(lhs, "syntax", None)
        if operator != "LeftShift" or syntax is None:
            return None
        unsized = getattr(syntax, "sliceSize", None) is None
        slice_size = 1 if unsized else _streaming_slice_size(lhs)
        if slice_size is None:
            return None
        parts = []
        leaf_two_state = []
        total_width = 0
        for stream in lhs.streams:
            operand = getattr(stream, "operand", None)
            if operand is None:
                return None
            with_expr = getattr(stream, "withExpr", None)
            array_targets = (_fixed_array_stream_targets_with(
                sm, operand, with_expr, symbolic) if with_expr is not None else
                _fixed_array_stream_targets(sm, operand, symbolic))
            if array_targets is not None:
                targets = array_targets
            else:
                target, admitted = (select_target(sm, operand)
                                    if symbolic else
                                    legacy_blocking_target(sm, operand, True))
                if not admitted or target is None:
                    return None
                if target.get("kind") not in ("Ident", "BitSel", "PartSel",
                                               "SelectTarget"):
                    return None
                if target.get("kind") in ("BitSel", "PartSel"):
                    base = target.get("value")
                    if base is None or base.get("kind") != "Ident":
                        return None
                    if target.get("kind") == "BitSel":
                        if target.get("index", {}).get("kind") != "Int":
                            return None
                    elif (target.get("msb", {}).get("kind") != "Int"
                          or target.get("lsb", {}).get("kind") != "Int"):
                        return None
                targets = [target]
            if any(target.get("width") != slice_size for target in targets):
                return None
            parts.extend(targets)
            total_width += sum(target["width"] for target in targets)
            if symbolic:
                leaf_two_state.extend([bool(target.get("two_state", False))
                                       for target in targets])
        if not parts or total_width % slice_size != 0:
            return None
        value = _convert_streaming_source(sm, expr.right)
        if value is None:
            value = convert_expr(sm, expr.right)
        if (value is None or value.get("kind") == "Unsupported"
                or not _case_source_expression_ok(expr.right)
                or width_of(value) != total_width
                or not _case_expression_ok(value)):
            return None
        source_parts = []
        for offset in range(0, total_width, slice_size):
            if symbolic:
                source_parts.append({
                    "kind": "PartSel", "span": node_span(sm, expr.right),
                    "width": slice_size, "value": value,
                    "msb": {"kind": "Int", "span": node_span(sm, expr.right),
                            "value": offset + slice_size - 1},
                    "lsb": {"kind": "Int", "span": node_span(sm, expr.right),
                            "value": offset},
                })
            else:
                index_width = max(32, offset.bit_length())
                source_parts.append({
                    "kind": "SelectRead", "span": node_span(sm, expr.right),
                    "width": slice_size, "value": value,
                    "index": {"kind": "Literal", "span": node_span(sm, expr.right),
                               "width": index_width,
                               "bits": format(offset, "0%db" % index_width)},
                    "index_signed": False, "descending": False,
                })
        packed = {"kind": "Concat", "span": node_span(sm, expr.right),
                  "width": total_width, "parts": source_parts}
        if symbolic:
            if any(leaf_two_state) and not all(leaf_two_state):
                return None
            if all(leaf_two_state):
                packed = squash2_wrap(packed, total_width)
        target = {"kind": "ConcatTarget", "span": node_span(sm, lhs),
                  "width": total_width, "parts": parts}
        windows = _symbolic_target_windows(target)
        if windows is None or any(
                old_base == base and not (high < old_low or old_high < low)
                for i, (base, low, high) in enumerate(windows)
                for old_base, old_low, old_high in windows[:i]):
            return None
        return {"kind": "NonblockingAssign" if expr.isNonBlocking
                else "BlockingAssign", "span": node_span(sm, expr),
                "target": target, "value": packed}
    except Exception:
        return None


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
        token = getattr(getattr(lhs, "syntax", None), "operatorToken", None)
        operator = str(getattr(token, "kind", "")).split(".")[-1]
        if operator == "LeftShift":
            return _streaming_left_target_assignment(sm, expr, False)
        if operator != "RightShift":
            return None
        explicit_slice = _streaming_has_slice_size(lhs)
        slice_size = _streaming_slice_size(lhs) if explicit_slice else None
        if explicit_slice and slice_size is None:
            return None
        parts = []
        total_width = 0
        for stream in lhs.streams:
            operand = getattr(stream, "operand", None)
            if operand is None:
                return None
            with_expr = getattr(stream, "withExpr", None)
            if explicit_slice and with_expr is not None:
                return None
            array_targets = (_fixed_array_stream_targets_with(
                sm, operand, with_expr, False) if with_expr is not None else
                _fixed_array_stream_targets(sm, operand, False))
            if array_targets is not None:
                parts.extend(array_targets)
                total_width += sum(target["width"] for target in array_targets)
                continue
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
            if explicit_slice and width != slice_size:
                return None
            parts.append(target)
            total_width += width
        if explicit_slice and (not parts or total_width % slice_size != 0):
            return None
        if not parts:
            return None
        value = _convert_streaming_source(sm, expr.right)
        source_lowered = value is not None
        if value is None:
            value = convert_expr(sm, expr.right)
        if (value is None or value.get("kind") == "Unsupported"
                or (not source_lowered and not _case_source_expression_ok(expr.right))
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
        token = getattr(getattr(lhs, "syntax", None), "operatorToken", None)
        operator = str(getattr(token, "kind", "")).split(".")[-1]
        if operator == "LeftShift":
            return _streaming_left_target_assignment(sm, expr, True)
        if operator != "RightShift":
            return None
        explicit_slice = _streaming_has_slice_size(lhs)
        slice_size = _streaming_slice_size(lhs) if explicit_slice else None
        if explicit_slice and slice_size is None:
            return None
        parts = []
        total_width = 0
        leaf_two_state = []
        for stream in lhs.streams:
            operand = getattr(stream, "operand", None)
            if operand is None or getattr(stream, "withExpr", None) is not None:
                return None
            array_targets = _fixed_array_stream_targets(sm, operand, True)
            if array_targets is not None:
                parts.extend(array_targets)
                leaf_two_state.extend(
                    [target["two_state"] for target in array_targets])
                total_width += sum(target["width"] for target in array_targets)
                continue
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
            if explicit_slice and width != slice_size:
                return None
            try:
                leaf_two_state.append(not operand.type.isFourState)
            except Exception:
                return None
            parts.append(target)
            total_width += width
        if explicit_slice and (not parts or total_width % slice_size != 0):
            return None
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


def _pure_array_query_call(expression):
    """Recognize discarded no-``with`` queries on fixed integral arrays."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or getattr(expression, "bad", False)
                or not expression.isSystemCall
                or expression.subroutineName not in
                ("min", "max", "unique", "unique_index")
                or len(expression.arguments) != 1):
            return False
        receiver = expression.arguments[0]
        if (type(receiver).__name__ != "NamedValueExpression"
                or type(receiver.type.canonicalType).__name__
                != "FixedSizeUnpackedArrayType"):
            return False
        shape = _fixed_array_dimensions(receiver.type)
        if shape is None:
            return False
        _dimensions, element_type = shape
        if type(element_type.canonicalType).__name__ in (
                "PackedStructType", "PackedUnionType",
                "UnpackedStructType", "UnpackedUnionType"):
            return False
        width, _two_state, reason = type_width_2s(element_type)
        if width is None or reason is not None:
            return False
        info = getattr(expression.subroutine, "extraInfo", None)
        if info is None:
            return True
        if type(info).__name__ != "IteratorCallInfo":
            return False
        iter_expr = getattr(info, "iterExpr", None)
        if (iter_expr is None
                or not _case_source_expression_ok(iter_expr, packed_members=True)):
            return False
        iter_width, _iter_two_state, iter_reason = type_width_2s(iter_expr.type)
        if (iter_width is None or iter_reason is not None
                or type(iter_expr.type.canonicalType).__name__ in (
                    "PackedStructType", "PackedUnionType",
                    "UnpackedStructType", "UnpackedUnionType")):
            return False
        return True
    except Exception:
        return False


def _array_reduction_index_call(expression):
    """Recognize ``item.index()`` while lowering a finite array reduction."""
    try:
        if (_SYM is not None or type(expression).__name__ != "CallExpression"
                or not expression.isSystemCall
                or expression.subroutineName != "index"
                or len(expression.arguments) != 1):
            return False
        argument = expression.arguments[0]
        return (str(getattr(getattr(argument, "symbol", None), "kind", ""))
                == "SymbolKind.Iterator")
    except Exception:
        return False


def _convert_array_reduction_index(sm, expression):
    if not _array_reduction_index_call(expression):
        return unsupported(sm, expression, "ArrayReduction:iterator-index")
    value = _ARRAY_REDUCTION_INDICES.get(expression.arguments[0].symbol)
    if value is None:
        return unsupported(sm, expression, "ArrayReduction:iterator-index")
    width, _two_state, reason = type_width_2s(expression.type)
    if width is None or reason is not None:
        return unsupported(sm, expression, "ArrayReduction:iterator-index")
    return signed_metadata({
        "kind": "Literal", "span": node_span(sm, expression),
        "width": width, "bits": format(value % (1 << width), "0%db" % width),
        "array_reduction_index": True,
    }, expression.type)


def _array_reduction_shape(expression):
    """Return the finite unpacked dimensions available to a reduction.

    Reduction methods consume one unpacked dimension at a time.  Ordinary
    storage expressions use their flat array name; an iterator bound by an
    enclosing ``with`` expression uses the synthetic row name installed by
    ``_array_reduction_terms``.  Dynamic, queue, associative, and aggregate
    leaves remain outside this representation.
    """
    try:
        if type(expression).__name__ == "ConversionExpression":
            expression = getattr(expression, "operand", None)
            if expression is None:
                return None
        if _SYM is None and getattr(expression, "symbol", None) in _ARRAY_REDUCTION_VALUES:
            source_name = _ARRAY_REDUCTION_VALUES[expression.symbol].get("name")
            source_type = expression.type
        elif (_storage_expression(expression)
              and str(expression.symbol.kind) == "SymbolKind.Variable"):
            source_name = _array_storage_name(expression.symbol)
            source_type = expression.type
        elif (type(expression).__name__ == "NamedValueExpression"
              and str(getattr(expression.symbol, "kind", ""))
              == "SymbolKind.Iterator"):
            # Purity checking visits an inner reduction before its enclosing
            # iterator has been bound.  Its type still carries the complete
            # finite suffix shape; the concrete synthetic name is supplied
            # when the enclosing reduction converts its terms.
            source_name = getattr(expression.symbol, "name", None)
            source_type = expression.type
        else:
            return None
        if type(source_type.canonicalType).__name__ == "DynamicArrayType":
            count = (_dynamic_array_constant_extent(expression.symbol)
                     if getattr(expression, "symbol", None) is not None else None)
            if count is None:
                return None
            inner = _dynamic_array_element_shape(source_type.canonicalType.elementType)
            if inner is None:
                element_type = source_type.canonicalType.elementType
                if type(element_type.canonicalType).__name__ != "UnpackedStructType":
                    return None
                shape = ([(0, count - 1)], element_type)
            else:
                inner_dimensions, leaf_type, _inner_width, _inner_two = inner
                shape = ([(0, count - 1)] + inner_dimensions, leaf_type)
        else:
            shape = _fixed_array_dimensions(source_type)
        if shape is None:
            return None
        dimensions, leaf_type = shape
        width, two_state, reason = type_width_2s(leaf_type)
        if (source_name is None
                or (width is None and type(leaf_type.canonicalType).__name__
                    != "UnpackedStructType")
                or (width is not None and reason is not None)):
            return None
        return source_name, width, two_state, dimensions, leaf_type
    except Exception:
        return None


def _empty_dynamic_array_reduction(expression):
    """Recognize an untouched, default-empty dynamic array reduction.

    An uninitialized dynamic array has size zero.  The flat state does not
    need an aggregate slot for this case: the reduction's empty result is a
    scalar identity, provided no source occurrence can resize, write, or
    select an element of the array.
    """
    try:
        if type(expression).__name__ != "CallExpression" or len(expression.arguments) != 1:
            return False
        argument = expression.arguments[0]
        if type(argument).__name__ == "ConversionExpression":
            argument = getattr(argument, "operand", None)
        symbol = getattr(argument, "symbol", None)
        if (symbol is None or str(getattr(symbol, "kind", "")) != "SymbolKind.Variable"
                or type(symbol.type.canonicalType).__name__ != "DynamicArrayType"
                or getattr(symbol, "initializer", None) is not None):
            return False
        instance = getattr(getattr(symbol, "parentScope", None),
                           "containingInstance", None)
        if instance is None:
            return False
        valid = True

        def inspect(node):
            nonlocal valid
            if node is expression:
                return
            kind = type(node).__name__
            if kind == "AssignmentExpression":
                lhs = getattr(node, "left", None)
                if (type(lhs).__name__ == "NamedValueExpression"
                        and getattr(lhs, "symbol", None) is symbol):
                    valid = False
            elif kind == "ElementSelectExpression":
                value = getattr(node, "value", None)
                if getattr(value, "symbol", None) is symbol:
                    valid = False

        instance.visit(inspect)
        return valid
    except Exception:
        return False


def _array_reduction_source_ok(expression):
    if expression.bad or len(expression.arguments) != 1:
        return False
    shape = _array_reduction_shape(expression.arguments[0])
    if shape is None and not _empty_dynamic_array_reduction(expression):
        return False
    info = expression.subroutine.extraInfo
    return info is None or (type(info).__name__ == "IteratorCallInfo"
                            and _case_source_expression_ok(info.iterExpr, packed_members=True))


def _array_reduction_terms(sm, expression, shape):
    name, width, _two_state, dimensions, leaf_type = shape
    left, right = dimensions[0]
    info = expression.subroutine.extraInfo
    parts = []
    for position in range(left, right + (1 if right >= left else -1), 1 if right >= left else -1):
        row_name = f"{name}[{position}]"
        if type(leaf_type.canonicalType).__name__ == "UnpackedStructType":
            value = {"name": row_name, "aggregate": leaf_type}
        else:
            value = signed_metadata({"kind": "Ident", "span": node_span(sm, expression),
                                     "name": row_name, "width": width},
                                    expression.arguments[0].type.canonicalType.elementType)
        if info is not None:
            previous = dict(_ARRAY_REDUCTION_VALUES)
            previous_indices = dict(_ARRAY_REDUCTION_INDICES)
            _ARRAY_REDUCTION_VALUES[info.iterVar] = value
            _ARRAY_REDUCTION_INDICES[info.iterVar] = position
            try:
                value = convert_expr(sm, info.iterExpr)
            finally:
                _ARRAY_REDUCTION_VALUES.clear()
                _ARRAY_REDUCTION_VALUES.update(previous)
                _ARRAY_REDUCTION_INDICES.clear()
                _ARRAY_REDUCTION_INDICES.update(previous_indices)
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
    if _empty_dynamic_array_reduction(expression):
        if expression.subroutineName not in ("sum", "product"):
            return unsupported(sm, expression, "ArrayReduction:storage-or-effects")
        if info is not None and not _case_source_expression_ok(
                info.iterExpr, packed_members=True):
            return unsupported(sm, expression, "ArrayReduction:with-expression")
        return signed_metadata({
            "kind": "Literal", "span": node_span(sm, expression),
            "width": width, "bits": "0" * width,
            "array_reduction_lowered": expression.subroutineName,
            "empty_array_reduction": True,
        }, expression.type)
    parts = _array_reduction_terms(sm, expression, _array_reduction_shape(expression.arguments[0]))
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
    if _SYM is None and _time_call(node):
        return len(node.arguments) == 0
    if _SYM is None and _fopen_invalid_mode_call(node):
        return True
    if _SYM is None and _clog2_call(node):
        return len(node.arguments) == 1 and all(
            _case_source_expression_ok(argument, packed_members=packed_members)
            for argument in node.arguments)
    if _SYM is None and _array_reduction_call(node):
        return _array_reduction_source_ok(node)
    if _SYM is None and _array_reduction_index_call(node):
        return True
    if _SYM is None and _string_literal_getc_method(node):
        return True
    if (type(node).__name__ == "CallExpression"
            and _enum_method_call(node, include_name=True)):
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
        if kind == "MemberAccessExpression":
            container = node.value.type.canonicalType
            if type(container).__name__ == "UnpackedUnionType":
                pure = pure and _unpacked_struct_member(None, node) is not None
                return
        if kind == "MemberAccessExpression" and packed_members:
            container = node.value.type.canonicalType
            if type(container).__name__ in ("PackedStructType", "PackedUnionType"):
                pure = pure and not getattr(container, "isTagged", False)
            elif type(container).__name__ == "UnpackedStructType":
                pure = pure and _unpacked_struct_member(None, node) is not None
            elif type(container).__name__ == "UnpackedUnionType":
                pure = pure and _unpacked_struct_member(None, node) is not None
            else:
                pure = False
            return
        pure = pure and not getattr(node, "bad", False) and kind in (
            "IntegerLiteral", "UnbasedUnsizedIntegerLiteral", "StringLiteral",
            "TimeLiteral",
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
    if _SYM is None and (expr.isNonBlocking or expr.timingControl is not None):
        lhs_type = getattr(expr.left, "type", None)
        union_lhs = _unpacked_union_shape(lhs_type) is not None
        if type(expr.left).__name__ == "MemberAccessExpression":
            union_lhs = union_lhs or (
                _unpacked_union_shape(getattr(expr.left.value, "type", None))
                is not None)
        if union_lhs:
            return unsupported(sm, span_node or expr,
                               "AssignmentExpression:target")
    whole_union = _unpacked_union_whole_copy(sm, expr)
    if whole_union is not None:
        return whole_union
    # A direct class-handle null write only updates opaque storage.  Restrict
    # this to a named variable: member receivers and selected targets can
    # have observable evaluation or aliasing effects.  Construction and all
    # nonblocking/timed forms remain outside the erased slice.
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(getattr(expr.left.type, "canonicalType", None)).__name__
            in ("ClassType", "CHandleType", "VirtualInterfaceType", "EventType")
            and _null_literal(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "opaque_handle_null_write": True}
    # ``process::self()`` returns an opaque process handle.  The flat
    # self-check state has no process object slot, so erase only this direct
    # blocking write; status/method reads and every other process operation
    # stay outside this admission rather than inventing process identity or
    # scheduling.
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(getattr(expr.left.type, "canonicalType", None)).__name__
            == "ClassType"
            and getattr(expr.left.type.canonicalType, "name", None) == "process"
            and type(expr.right).__name__ == "CallExpression"
            and getattr(expr.right, "subroutineName", None) == "self"
            and not getattr(expr.right, "arguments", [])):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "opaque_process_self_write": True}
    # An unbounded mailbox construction has no flat self-check state.  Erase
    # only the exact built-in ``mailbox box = new()`` write: bounded and
    # argumented constructors, user classes, and every later method/read stay
    # loud rather than fabricating an object or constructor effect.
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(getattr(expr.left.type, "canonicalType", None)).__name__
            == "ClassType"
            and getattr(expr.left.type.canonicalType, "name", None) == "mailbox"
            and _bare_new(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "opaque_mailbox_new_write": True}
    # A zero-key semaphore likewise has no represented object state.  Restrict
    # this to the literal built-in constructor shape; nonzero key counts and
    # every later synchronization operation remain loud.
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(getattr(expr.left.type, "canonicalType", None)).__name__
            == "ClassType"
            and getattr(expr.left.type.canonicalType, "name", None) == "semaphore"
            and _explicit_new_zero(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "opaque_semaphore_zero_write": True}
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(getattr(expr.left.type, "canonicalType", None)).__name__
            == "ClassType"
            and getattr(expr.left.type.canonicalType, "name", None) == "semaphore"
            and _semaphore_new_nonnegative_literal(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "opaque_semaphore_literal_new_write": True}
    # Real and shortreal values have no representation in the flat
    # self-check state.  A pure literal blocking write consequently has no
    # modeled effect and can be erased.  Keep nonblocking writes, names,
    # calls, arithmetic, and all reads loud: those can affect scheduling or
    # observations outside this opaque-storage slice.
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(getattr(expr.left.type, "canonicalType", None)).__name__
            == "FloatingType"
            and _floating_literal(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "floating_literal_write_noop": True}
    # The same opaque boundary applies to a side-effect-free IEEE math or
    # real-conversion system call.  Keep named storage only; selectors and
    # effectful arguments retain their ordinary target boundary.
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(getattr(expr.left.type, "canonicalType", None)).__name__
            == "FloatingType"
            and _floating_pure_call(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "floating_pure_call_write_noop": True}
    # ``string.atoreal()`` is likewise a pure conversion when its receiver's
    # ASCII literal history is proven.  Real storage is opaque in the
    # self-check state, so discard only this direct blocking write; reads,
    # aliases, dynamic strings, and scheduled forms remain loud.
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(getattr(expr.left.type, "canonicalType", None)).__name__
            == "FloatingType"
            and _floating_string_atoreal_call(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "floating_string_atoreal_write_noop": True}
    # `$realtime` is fixed at zero in the self-check time-zero slice, while
    # real storage remains opaque.  Erase only this blocking write; integer
    # targets, timed/nonblocking forms, and real reads stay loud.
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(getattr(expr.left.type, "canonicalType", None)).__name__
            == "FloatingType"
            and _realtime_call(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "realtime_write_noop": True}
    # An opaque string has no flat-state slot. A pure literal write has no
    # effect of its own, so it can be erased; later string reads still lower
    # to their existing loud boundary. Nonliteral writes remain unsupported.
    if (_SYM is None and expr.op is None
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(expr.left.type.canonicalType).__name__ == "StringType"
            and type(expr.right).__name__ == "ConversionExpression"
            and type(getattr(expr.right, "operand", None)).__name__ == "StringLiteral"
            and not getattr(expr.right, "bad", False)
            and not getattr(expr.right.operand, "bad", False)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "string_literal_write_noop": True}
    # The same opaque boundary is safe for a literal-only concatenation, but
    # preserve the ordinary timing and publication boundaries for this new
    # shape. Dynamic operands and replication remain loud.
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(expr.left.type.canonicalType).__name__ == "StringType"
            and type(expr.right).__name__ == "ConversionExpression"
            and type(getattr(expr.right, "operand", None)).__name__ == "ConcatenationExpression"
            and _string_literal_write(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "string_literal_concat_write_noop": True}
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(expr.left.type.canonicalType).__name__ == "StringType"
            and type(expr.right).__name__ == "ConversionExpression"
            and type(getattr(expr.right, "operand", None)).__name__ == "ReplicationExpression"
            and _string_literal_write(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "string_literal_replication_write_noop": True}
    # An empty queue literal likewise carries no state in the flat self-check
    # store. Keep nonempty queue construction and observations loud.
    if (_SYM is None and _queue_literal_write_noop(expr)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "queue_literal_write_noop": True}
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(expr.left.type.canonicalType).__name__ == "QueueType"
            and _empty_queue_literal(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "empty_queue_write_noop": True}
    # A zero-item dynamic-array literal has the same unrepresented-state
    # boundary. Later size/element reads remain loud.
    if (_SYM is None and expr.op is None and expr.timingControl is None
            and not expr.isNonBlocking
            and type(expr.left).__name__ == "NamedValueExpression"
            and type(expr.left.type.canonicalType).__name__ == "DynamicArrayType"
            and _empty_queue_literal(expr.right)):
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "empty_dynamic_array_write_noop": True}
    if expr.timingControl is not None:
        return _convert_intra_assignment(sm, expr)
    scan = _convert_scan_assignment(sm, expr)
    if scan is not None:
        return scan
    if expr.op is None:
        if _SYM is None:
            dist_uniform_scalar = _dist_uniform_scalar_assignment(sm, expr)
            if dist_uniform_scalar is not None:
                return dist_uniform_scalar
            dist_uniform_target = _dist_uniform_fixed_array_assignment(sm, expr)
            if dist_uniform_target is not None:
                return dist_uniform_target
        dynamic_streaming_target = (
            _dynamic_streaming_with_target_assignment(sm, expr)
            if _SYM is None else None)
        if dynamic_streaming_target is not None:
            return dynamic_streaming_target
        streaming_target = (
            _symbolic_streaming_target_assignment(sm, expr)
            if _SYM is not None else _streaming_target_assignment(sm, expr))
        if streaming_target is not None:
            return streaming_target
    if expr.op is None and _SYM is None:
        dynamic_new_pattern = _dynamic_array_new_pattern_assignment(sm, expr)
        if dynamic_new_pattern is not None:
            return dynamic_new_pattern
        dynamic_concat = _dynamic_array_concat_assignment(sm, expr)
        if dynamic_concat is not None:
            return dynamic_concat
        dynamic_pattern = _dynamic_array_pattern_assignment(sm, expr)
        if dynamic_pattern is not None:
            return dynamic_pattern
        dynamic_resize_copy = _dynamic_array_resize_copy_assignment(sm, expr)
        if dynamic_resize_copy is not None:
            return dynamic_resize_copy
        dynamic_allocation = _dynamic_array_allocation_assignment(sm, expr)
        if dynamic_allocation is not None:
            return dynamic_allocation
        dynamic_fixed_mismatch = _dynamic_fixed_size_mismatch(sm, expr)
        if dynamic_fixed_mismatch is not None:
            return dynamic_fixed_mismatch
        queue_struct_pop = _queue_empty_pop_struct_assignment(sm, expr)
        if queue_struct_pop is not None:
            return queue_struct_pop
        struct_pattern = _unpacked_struct_pattern_assignment(sm, expr)
        if struct_pattern is not None:
            return struct_pattern
        struct_copy = _unpacked_struct_copy_assignment(sm, expr)
        if struct_copy is not None:
            return struct_copy
        struct_conditional = _unpacked_struct_conditional_assignment(sm, expr)
        if struct_conditional is not None:
            return struct_conditional
        array_pattern_lhs = _fixed_array_pattern_lhs_assignment(sm, expr)
        if array_pattern_lhs is not None:
            return array_pattern_lhs
        array_nested_pattern = _fixed_array_nested_pattern_assignment(sm, expr)
        if array_nested_pattern is not None:
            return array_nested_pattern
        array_struct_copy = _fixed_array_struct_copy_assignment(sm, expr)
        if array_struct_copy is not None:
            return array_struct_copy
        array_slice = _fixed_array_slice_pattern_assignment(sm, expr)
        if array_slice is not None:
            return array_slice
        array_concat = _fixed_array_concat_assignment(sm, expr)
        if array_concat is not None:
            return array_concat
        array_subarray_pattern = _fixed_array_subarray_pattern_assignment(sm, expr)
        if array_subarray_pattern is not None:
            return array_subarray_pattern
        array_dynamic_subarray_read_copy = _fixed_array_dynamic_subarray_read_copy_assignment(sm, expr)
        if array_dynamic_subarray_read_copy is not None:
            return array_dynamic_subarray_read_copy
        array_dynamic_subarray_copy = _fixed_array_dynamic_subarray_copy_assignment(sm, expr)
        if array_dynamic_subarray_copy is not None:
            return array_dynamic_subarray_copy
        array_subarray_copy = _fixed_array_subarray_copy_assignment(sm, expr)
        if array_subarray_copy is not None:
            return array_subarray_copy
        array_conditional = _fixed_array_conditional_assignment(sm, expr)
        if array_conditional is not None:
            return array_conditional
        array_dynamic_slice = _fixed_array_dynamic_slice_assignment(sm, expr)
        if array_dynamic_slice is not None:
            return array_dynamic_slice
        array_bitstream_cast = _fixed_array_bitstream_cast_assignment(sm, expr)
        if array_bitstream_cast is not None:
            return array_bitstream_cast
        array_struct_pattern = _fixed_array_struct_pattern_assignment(sm, expr)
        if array_struct_pattern is not None:
            return array_struct_pattern
        array_nested_copy = _fixed_array_nested_copy_assignment(sm, expr)
        if array_nested_copy is not None:
            return array_nested_copy
        array_copy = _fixed_array_copy_assignment(sm, expr)
        if array_copy is not None:
            return array_copy
        nested_dynamic_array = _fixed_array_nested_dynamic_assignment(sm, expr)
        if nested_dynamic_array is not None:
            return nested_dynamic_array
        dynamic_array = _fixed_array_dynamic_assignment(sm, expr)
        if dynamic_array is not None:
            return dynamic_array
        array_assignment = _fixed_array_pattern_assignment(sm, expr)
        if array_assignment is not None:
            return array_assignment
    if expr.op is not None:
        return _convert_compound_assignment(sm, expr, span_node)
    if (_SYM is None and _invalid_struct_replication_assignment(expr)
            and not expr.isNonBlocking):
        # §5.10 forbids replication in a structure assignment pattern.  The
        # elaboration-invalid write has no runtime effect in the self-check
        # tier, so retain only inert metadata rather than aggregate storage.
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "invalid_struct_replication_assignment": True}
    if (_SYM is None and _invalid_string_unknown_replication(expr)
            and not expr.isNonBlocking):
        # §6.16 requires a nonnegative, fully known integral multiplier for
        # string replication; an x/z multiplier is an elaboration error.
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "invalid_string_replication_multiplier": True}
    if (_SYM is None and _invalid_associative_index_target(expr.left)
            and not expr.isNonBlocking):
        # §7.8.4/§7.8.5 reject floating associative keys and implicit
        # real-to-integral key conversions at elaboration.  The rejected write
        # has no runtime effect in the self-check tier.
        return {"kind": "Empty", "span": node_span(sm, span_node or expr),
                "invalid_associative_index_target": True}
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
        oob_struct = _unpacked_struct_oob_assignment(sm, expr)
        if oob_struct is not None:
            return oob_struct
        if expr.op is None and type(expr.left).__name__ == "ElementSelectExpression":
            cell = _fixed_array_cell(sm, expr.left)
            base = expr.left.value
            if (cell is not None and
                    type(base.type.canonicalType).__name__ == "DynamicArrayType"
                    and _case_source_expression_ok(expr.right)):
                name, width, two_state = cell
                value = convert_expr(sm, expr.right)
                if (value is not None and _case_expression_ok(value)
                        and width_of(value) == width):
                    if two_state:
                        value = squash2_wrap(value, width)
                    return {
                        "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
                        "span": node_span(sm, span_node or expr),
                        "target": {"kind": "Ident", "span": node_span(sm, expr.left),
                                   "width": width, "name": name},
                        "value": value,
                        "dynamic_array_cell_lowered": True,
                    }
        target, ok = legacy_blocking_target(sm, expr.left)
    else:
        target, ok = select_target(sm, expr.left)
    if not ok:
        return unsupported(sm, span_node or expr, "AssignmentExpression:target")
    if (target.get("kind") in ("SelectTarget", "ConcatTarget")
            and not _case_source_expression_ok(expr.right, packed_members=_SYM is None)):
        return unsupported(sm, span_node or expr, "AssignmentExpression:selected-effects")
    value = convert_expr(sm, expr.right)
    mailbox_try_get_target = None
    mailbox_try_get_value = None
    if isinstance(value, dict) and value.get("mailbox_literal_try_get_target") is not None:
        mailbox_try_get_target = value["mailbox_literal_try_get_target"]
        mailbox_try_get_value = value.get("mailbox_literal_try_get_value")
        value = dict(value)
        value.pop("mailbox_literal_try_get_target", None)
        value.pop("mailbox_literal_try_get_value", None)
    try:
        if not expr.left.type.isFourState:
            value = squash2_wrap(value, expr.left.type.bitWidth)
    except Exception:
        pass
    result = {
        "kind": "NonblockingAssign" if expr.isNonBlocking else "BlockingAssign",
        "span": node_span(sm, span_node or expr),
        "target": target,
        "value": value,
    }
    if mailbox_try_get_target is not None and mailbox_try_get_value is not None:
        return {
            "kind": "Block",
            "span": node_span(sm, span_node or expr),
            "stmts": [
                {"kind": "BlockingAssign",
                 "span": node_span(sm, expr.right),
                 "target": mailbox_try_get_target,
                 "value": mailbox_try_get_value,
                 "mailbox_literal_try_get": True},
                result,
            ],
            "mailbox_literal_try_get_assignment": True,
        }
    return result


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
    if _SYM is None and is_chandle_decl(symbol):
        if getattr(symbol, "initializer", None) is not None:
            return unsupported(sm, stmt, "VariableDeclStatement:chandle-initializer")
        return {"kind": "Empty", "span": node_span(sm, stmt)}
    if _SYM is None and is_inert_class_handle_decl(symbol):
        return {"kind": "Empty", "span": node_span(sm, stmt)}
    if _SYM is None and is_literal_semaphore_decl(symbol):
        return {"kind": "Empty", "span": node_span(sm, stmt),
                "opaque_semaphore_literal_new_write": True}
    if _SYM is None and is_string_decl(symbol):
        return {"kind": "Empty", "span": node_span(sm, stmt)}
    if _SYM is None and is_inert_2state_floating_decl(symbol):
        return {"kind": "Empty", "span": node_span(sm, stmt)}
    if _SYM is None and is_inert_2state_queue_decl(symbol):
        return {"kind": "Empty", "span": node_span(sm, stmt)}
    if _SYM is None and is_inert_2state_dynamic_array_decl(symbol):
        return {"kind": "Empty", "span": node_span(sm, stmt)}
    if _SYM is None:
        assoc_decls = _finite_string_assoc_decls(sm, symbol)
        if assoc_decls is not None:
            lifetime = str(symbol.lifetime).split(".")[-1]
            if lifetime == "Automatic":
                return {"kind": "Block", "span": node_span(sm, stmt), "stmts": [
                    {"kind": "LocalDecl", "span": cell["span"],
                     "name": cell["name"], "width": cell["width"],
                     "two_state": cell.get("two_state", False),
                     "init": cell.get("init")}
                    for cell in assoc_decls]}
            if lifetime == "Static":
                return {"kind": "Empty", "span": node_span(sm, stmt)}
            return unsupported(sm, stmt, "VariableDeclStatement:array-lifetime")
        assoc_decls = _finite_integral_assoc_decls(sm, symbol)
        if assoc_decls is not None:
            lifetime = str(symbol.lifetime).split(".")[-1]
            if lifetime == "Automatic":
                return {"kind": "Block", "span": node_span(sm, stmt), "stmts": [
                    {"kind": "LocalDecl", "span": cell["span"],
                     "name": cell["name"], "width": cell["width"],
                     "two_state": cell.get("two_state", False),
                     "init": cell.get("init")}
                    for cell in assoc_decls]}
            if lifetime == "Static":
                return {"kind": "Empty", "span": node_span(sm, stmt)}
            return unsupported(sm, stmt, "VariableDeclStatement:array-lifetime")
    if _SYM is None and is_inert_2state_associative_array_decl(symbol):
        return {"kind": "Empty", "span": node_span(sm, stmt)}
    if _SYM is None:
        union_decl = _unpacked_union_decls(sm, symbol)
        if union_decl is not None:
            return {"kind": "LocalDecl", "span": union_decl["span"],
                    "name": union_decl["name"],
                    "width": union_decl["width"],
                    "two_state": union_decl.get("two_state", False),
                    "init": union_decl.get("init"),
                    "automatic_union": True}
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


def _sformat_literal_assignment(sm, expression):
    """Lower ``$sformat`` of a plain literal into an integral assignment.

    IEEE 1800-2023 §21.3.3 applies the string-literal assignment rule (§5.9):
    the bytes are right aligned in the packed destination, with left padding
    or truncation.  Restrict this to a direct integral target and one literal
    format with no conversion markers; dynamic formats, arguments, selected
    effects, and string destinations remain on the call boundary.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or not expression.isSystemCall
                or expression.subroutineName != "$sformat"
                or getattr(expression, "timingControl", None) is not None):
            return None
        arguments = list(expression.arguments)
        if len(arguments) != 2:
            return None
        output, format_expr = arguments
        if (type(output).__name__ != "AssignmentExpression"
                or output.op is not None
                or output.timingControl is not None
                or output.isNonBlocking
                or type(format_expr).__name__ != "StringLiteral"
                or getattr(format_expr, "bad", False)
                or "%" in format_expr.value
                or _contains_disputed_string_escape(format_expr)):
            return None
        target_expr = output.left
        if (not getattr(target_expr.type, "isIntegral", False)
                or type(target_expr.type.canonicalType).__name__ in (
                    "StringType", "FloatingType")):
            return None
        width, two_state, reason = type_width_2s(target_expr.type)
        if width is None or reason is not None or width == 0 or width % 8:
            return None
        target, admitted = legacy_blocking_target(sm, target_expr)
        if not admitted or target.get("kind") != "Ident":
            return None
        try:
            data = format_expr.value.encode("latin-1")
        except (UnicodeEncodeError, Exception):
            return None
        source_bits = "".join(format(byte, "08b") for byte in data)
        if len(source_bits) > width:
            source_bits = source_bits[-width:]
        value = {"kind": "Literal", "span": node_span(sm, format_expr),
                 "width": width,
                 "bits": source_bits.rjust(width, "0"),
                 "sformat_literal": True}
        if two_state:
            value = squash2_wrap(value, width)
        return {"kind": "BlockingAssign", "span": node_span(sm, expression),
                "target": target, "value": value,
                "sformat_literal_assignment": True}
    except Exception:
        return None


def _format_literal_integral_text(format_text, arguments):
    """Render the small constant format slice used by packed writes."""
    specs = {
        "%b": ("b", 1), "%0b": ("b", 1),
        "%o": ("o", 1), "%0o": ("o", 1),
        "%h": ("h", 1), "%0h": ("h", 1),
        "%d": ("d", 1), "%0d": ("d", 1),
        "%s": ("s", 1),
    }
    if format_text == "%s:%0d":
        pieces = ("s", "d")
    else:
        spec = specs.get(format_text)
        if spec is None:
            return None
        pieces = (spec[0],)
    if len(arguments) != len(pieces):
        return None
    rendered = []
    for kind, argument in zip(pieces, arguments):
        node = argument
        while type(node).__name__ == "ConversionExpression":
            node = getattr(node, "operand", None)
            if node is None:
                return None
        if kind == "s":
            if type(node).__name__ != "StringLiteral" or getattr(node, "bad", False):
                return None
            rendered.append(node.value)
            continue
        if type(node).__name__ not in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
            return None
        if getattr(node, "bad", False):
            return None
        if kind == "b":
            rendered.append(svint_bits(node.value))
        elif kind == "o":
            value = _literal_integral_value(node)
            if value is None or value < 0:
                return None
            rendered.append(format(value, "o"))
        elif kind == "h":
            value = _literal_integral_value(node)
            if value is None or value < 0:
                return None
            rendered.append(format(value, "x"))
        else:
            value = _literal_integral_value(node)
            if value is None:
                return None
            rendered.append(str(value))
    text = "".join(rendered)
    try:
        text.encode("latin-1")
    except (UnicodeEncodeError, Exception):
        return None
    return text


def _literal_integral_bits(expression):
    """Return the exact four-state spelling of a direct integral literal."""
    node = expression
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return None
    if type(node).__name__ not in ("IntegerLiteral", "UnbasedUnsizedIntegerLiteral"):
        return None
    try:
        bits = svint_bits(node.value)
    except Exception:
        return None
    return bits if bits and all(bit in "01xz" for bit in bits) else None


def _default_radix_text(bits, radix):
    """Render a packed value using the task-selected b/o/h radix.

    A group containing an unknown bit is rendered with the corresponding
    unknown digit, matching the IEEE system-task spelling.  Known groups use
    lower-case hexadecimal digits; the caller supplies the complete packed
    width, so leading groups are retained.
    """
    if radix == "b":
        return bits
    group = 3 if radix == "o" else 4
    padded = bits.rjust(((len(bits) + group - 1) // group) * group, "0")
    digits = "0123456789abcdef"
    rendered = []
    for start in range(0, len(padded), group):
        chunk = padded[start:start + group]
        if "x" in chunk:
            rendered.append("x")
        elif "z" in chunk:
            rendered.append("z")
        else:
            rendered.append(digits[int(chunk, 2)])
    return "".join(rendered)


def _constant_default_radix_integral_assignment(sm, expression):
    """Lower a literal-source ``$swriteb/o/h`` packed write.

    The source value must be established by a direct blocking integral
    literal assignment before this call.  This keeps the lowering source
    ordered and preserves X/Z radix spelling without introducing a string
    runtime object; all other task forms remain loud.
    """
    try:
        if (type(expression).__name__ != "CallExpression"
                or not expression.isSystemCall
                or expression.subroutineName not in ("$swriteb", "$swriteo", "$swriteh")
                or getattr(expression, "timingControl", None) is not None):
            return None
        arguments = list(expression.arguments)
        if len(arguments) != 2:
            return None
        output, source = arguments
        if (type(output).__name__ != "AssignmentExpression"
                or output.op is not None
                or output.timingControl is not None
                or output.isNonBlocking
                or type(output.right).__name__ != "EmptyArgumentExpression"
                or type(source).__name__ != "NamedValueExpression"):
            return None
        target_expr = output.left
        if (type(target_expr).__name__ != "NamedValueExpression"
                or not getattr(target_expr.type, "isIntegral", False)):
            return None
        target_width, target_two_state, reason = type_width_2s(target_expr.type)
        source_width, _source_two_state, source_reason = type_width_2s(source.type)
        if (target_width is None or target_two_state is None or reason is not None
                or source_width is None or source_reason is not None
                or target_width <= 0 or target_width % 8 or source_width <= 0):
            return None
        target, admitted = legacy_blocking_target(sm, target_expr)
        if not admitted or target.get("kind") != "Ident":
            return None

        source_symbol = getattr(source, "symbol", None)
        instance = getattr(getattr(source_symbol, "parentScope", None),
                           "containingInstance", None)
        call_start = getattr(getattr(getattr(expression, "sourceRange", None),
                                     "start", None), "offset", None)
        if source_symbol is None or instance is None or call_start is None:
            return None

        assignments = []
        invalid_write = False

        def inspect(node):
            nonlocal invalid_write
            if type(node).__name__ != "AssignmentExpression":
                return
            lhs = getattr(node, "left", None)
            if (getattr(lhs, "symbol", None) is not source_symbol
                    or type(lhs).__name__ != "NamedValueExpression"):
                return
            offset = getattr(getattr(getattr(node, "sourceRange", None),
                                     "start", None), "offset", None)
            if offset is None or offset >= call_start:
                return
            if (node.op is not None or node.timingControl is not None
                    or node.isNonBlocking):
                invalid_write = True
                return
            bits = _literal_integral_bits(getattr(node, "right", None))
            if bits is None:
                invalid_write = True
                return
            assignments.append((offset, bits))

        instance.visit(inspect)
        if invalid_write or not assignments:
            return None
        assignments.sort(key=lambda item: item[0])
        bits = assignments[-1][1]
        if len(bits) != source_width:
            return None
        text = _default_radix_text(bits, expression.subroutineName[-1])
        try:
            data = text.encode("latin-1")
        except (UnicodeEncodeError, Exception):
            return None
        source_bits = "".join(format(byte, "08b") for byte in data)
        if len(source_bits) > target_width:
            source_bits = source_bits[-target_width:]
        value = {"kind": "Literal", "span": node_span(sm, expression),
                 "width": target_width,
                 "bits": source_bits.rjust(target_width, "0"),
                 "default_radix_assignment": expression.subroutineName}
        if target_two_state:
            value = squash2_wrap(value, target_width)
        return {"kind": "BlockingAssign", "span": node_span(sm, expression),
                "target": target, "value": value,
                "default_radix_integral_assignment": expression.subroutineName}
    except Exception:
        return None


def _constant_formatted_integral_assignment(sm, expression):
    """Lower constant `$sformat`/`$swrite` output to a packed assignment."""
    try:
        if (type(expression).__name__ != "CallExpression"
                or not expression.isSystemCall
                or expression.subroutineName not in ("$sformat", "$swrite")
                or getattr(expression, "timingControl", None) is not None):
            return None
        arguments = list(expression.arguments)
        if len(arguments) < 3:
            return None
        output = arguments[0]
        format_expr = arguments[1]
        if (type(output).__name__ != "AssignmentExpression"
                or output.op is not None
                or output.timingControl is not None
                or output.isNonBlocking
                or type(format_expr).__name__ != "StringLiteral"
                or getattr(format_expr, "bad", False)
                or _contains_disputed_string_escape(format_expr)):
            return None
        target_expr = output.left
        if (not getattr(target_expr.type, "isIntegral", False)
                or type(target_expr.type.canonicalType).__name__ == "StringType"):
            return None
        width, two_state, reason = type_width_2s(target_expr.type)
        if width is None or reason is not None or width == 0 or width % 8:
            return None
        target, admitted = legacy_blocking_target(sm, target_expr)
        if not admitted or target.get("kind") not in ("Ident", "SelectTarget"):
            return None
        text = _format_literal_integral_text(format_expr.value, arguments[2:])
        if text is None:
            return None
        data = text.encode("latin-1")
        source_bits = "".join(format(byte, "08b") for byte in data)
        if len(source_bits) > width:
            source_bits = source_bits[-width:]
        value = {"kind": "Literal", "span": node_span(sm, format_expr),
                 "width": width, "bits": source_bits.rjust(width, "0"),
                 "constant_format_assignment": True}
        if two_state:
            value = squash2_wrap(value, width)
        return {"kind": "BlockingAssign", "span": node_span(sm, expression),
                "target": target, "value": value,
                "constant_format_integral_assignment": True}
    except Exception:
        return None


def _severity_floating_source_ok(expression):
    """Recognize a side-effect-free real/time argument for a quiet task.

    Real values are intentionally opaque in the self-check state, so they
    cannot be converted to an ``SExpr`` for the diagnostic renderer.  A
    quiet severity task may still erase such an argument when its source is
    only a literal, a unary sign around a literal, a named real read, or a
    zero-time query.
    """
    node = expression
    while type(node).__name__ == "ConversionExpression":
        node = getattr(node, "operand", None)
        if node is None:
            return False
    kind = type(node).__name__
    if kind in ("RealLiteral", "ShortRealLiteral"):
        return not getattr(node, "bad", False)
    if kind == "NamedValueExpression":
        try:
            return (not getattr(node, "bad", False)
                    and type(node.type.canonicalType).__name__ == "FloatingType")
        except Exception:
            return False
    if kind == "UnaryExpression":
        op = str(getattr(node, "op", "")).split(".")[-1]
        return op in ("Plus", "Minus", "UnaryPlus", "UnaryMinus") and \
            _severity_floating_source_ok(getattr(node, "operand", None))
    if kind == "CallExpression":
        return _realtime_call(node)
    return False


def _severity_argument_source_ok(expression):
    """Whether a quiet-task argument has no source-level side effects."""
    if _severity_floating_source_ok(expression):
        return True
    if type(expression).__name__ == "StringLiteral":
        return not getattr(expression, "bad", False)
    try:
        width, _two_state, reason = type_width_2s(expression.type)
        return (expression.type.isIntegral and width is not None
                and reason is None and _case_source_expression_ok(expression))
    except Exception:
        return False


def _convert_syscall(sm, s, e):
    """`$display`/`$write`/`$finish`/`$stop` in statement position ->
    `SysCall` node (self-check tier §f). `$display`/`$write` require the
    first argument to be a string literal (the format); the remaining args
    are M0/self-check expressions with a parallel `arg_signed` list (the
    Lean renderer needs signedness for `%d` widths and refuses to print
    negative signed values — the envelope carries no sign). `$finish`/
    `$stop` arguments (verbosity levels) are ignored. Any other call stays
    `Unsupported` (statement tag `ExpressionStatement:CallExpression`)."""
    if _SYM is None and _queue_empty_pop_method(e, allow_struct=True):
        # A discarded empty-queue pop has no represented result and leaves the
        # already-empty queue unchanged. Preserve the source-order proof used
        # by value-position empty pops while erasing only this void statement.
        return {"kind": "Empty", "span": node_span(sm, s),
                "queue_empty_pop_statement": e.subroutineName}
    if _SYM is None and _empty_aggregate_delete_method(e):
        # Deleting an already-empty queue or an uninitialized dynamic array
        # has no represented state effect. Keep the source-history and
        # zero-size checks in the recognizer; populated or effectful storage
        # remains on the ordinary call boundary.
        return {"kind": "Empty", "span": node_span(sm, s),
                "empty_aggregate_delete_statement": True}
    if _SYM is None and e.isSystemCall and e.subroutineName in ("$sformat", "$swrite"):
        constant_assignment = _constant_formatted_integral_assignment(sm, e)
        if constant_assignment is not None:
            return constant_assignment
    if _SYM is None and e.isSystemCall and e.subroutineName in (
            "$swriteb", "$swriteo", "$swriteh"):
        default_radix_assignment = _constant_default_radix_integral_assignment(sm, e)
        if default_radix_assignment is not None:
            return default_radix_assignment
    if _SYM is None and e.isSystemCall and e.subroutineName == "$q_initialize":
        status_assignment = _q_initialize_status_call(sm, e)
        if status_assignment is not None:
            return status_assignment
    if _SYM is None and e.isSystemCall and e.subroutineName == "$q_add":
        status_assignment = _q_add_status_call(sm, e)
        if status_assignment is not None:
            return status_assignment
    if _SYM is None and e.isSystemCall and e.subroutineName == "$q_full":
        status_assignment = _q_full_status_call(sm, e)
        if status_assignment is not None:
            return status_assignment
    if _SYM is None and e.isSystemCall and e.subroutineName == "$q_exam":
        status_assignment = _q_exam_status_call(sm, e)
        if status_assignment is not None:
            return status_assignment
    if _SYM is None and e.isSystemCall and e.subroutineName == "$q_remove":
        payload_assignment = _q_remove_payload_call(sm, e)
        if payload_assignment is not None:
            return payload_assignment
        status_assignment = _q_remove_status_call(sm, e)
        if status_assignment is not None:
            return status_assignment
    if _SYM is None and e.isSystemCall and e.subroutineName == "reverse":
        reversed_array = _fixed_array_reverse_method(sm, e)
        if reversed_array is not None:
            return reversed_array
    if _SYM is None and e.isSystemCall and e.subroutineName in ("sort", "rsort"):
        ordered_array = _fixed_array_ordering_method(sm, e)
        if ordered_array is not None:
            return ordered_array
    if _SYM is None and e.isSystemCall and e.subroutineName == "$sformat":
        literal_assignment = _sformat_literal_assignment(sm, e)
        if literal_assignment is not None:
            return literal_assignment
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
    if is_sys and _SYM is None and name == "$sformatf":
        # `$sformatf` is pure when its existing literal expression converter
        # accepts the format and operand.  In statement position the packed
        # result is discarded, so erase only that proven value; dynamic
        # formats, unsupported conversions, and effectful operands remain
        # loud through the same converter.
        value = _convert_sformatf_call(sm, e)
        if value is not None and value.get("kind") != "Unsupported":
            return {"kind": "Empty", "span": node_span(sm, s),
                    "sformatf_statement": True}
    if is_sys and _SYM is None and _enum_method_call(e, include_name=True):
        # Enum methods only read the current value and produce an unobserved
        # scalar in statement position. Reuse the value converter so receiver
        # effects and enum-member checks remain identical; malformed forms
        # stay loud.
        value = _convert_enum_method(sm, e)
        if value.get("kind") != "Unsupported":
            marker = ("enum_name_statement" if name == "name"
                      else "enum_numeric_statement")
            return {"kind": "Empty", "span": node_span(sm, s),
                    marker: name}
    if is_sys and _SYM is None and _pure_array_query_call(e):
        # Integral fixed-array locator queries only read their receiver and
        # return an unobserved queue.  Keep ``with`` clauses and aggregate or
        # dynamic storage on the ordinary call boundary.
        return {"kind": "Empty", "span": node_span(sm, s),
                "array_query_statement": name}
    if is_sys and _SYM is None and _array_reduction_call(e):
        # A pure array reduction only reads its source cells and produces an
        # unobserved scalar in statement position. Reuse the value converter
        # so storage shape, iterator bindings, widths, and effect checks stay
        # identical; dynamic or effectful reductions remain loud.
        value = _convert_array_reduction(sm, e)
        if value.get("kind") != "Unsupported":
            return {"kind": "Empty", "span": node_span(sm, s),
                    "array_reduction_statement": name}
    if not is_sys:
        if _semaphore_zero_method(e):
            # A zero-key semaphore method has no represented state effect;
            # retain the call's sequencing position as an ordinary no-op.
            return {"kind": "Empty", "span": node_span(sm, s),
                    "semaphore_zero_method": name}
        if _semaphore_literal_put_get(e):
            # A source-ordered literal balance proves that this put/get pair
            # completes without entering the scheduler. The handle itself is
            # intentionally outside the flat state; later literal try_get
            # expressions consume the same statically tracked balance.
            return {"kind": "Empty", "span": node_span(sm, s),
                    "semaphore_literal_method": name}
        if _dynamic_array_literal_size_method(e):
            return {"kind": "Empty", "span": node_span(sm, s),
                    "dynamic_array_literal_size": True}
        if _mailbox_empty_try_method(e):
            return {"kind": "Empty", "span": node_span(sm, s),
                    "mailbox_empty_try": name}
        if _semaphore_literal_try_get(e):
            # The result is discarded, but the source-ordered recognizer
            # accounts for this successful acquisition in later calls.
            return {"kind": "Empty", "span": node_span(sm, s),
                    "semaphore_literal_try_get": True}
        mailbox_get = _mailbox_literal_get_state(sm, e)
        if mailbox_get is not None:
            if name == "put":
                return {"kind": "Empty", "span": node_span(sm, s),
                        "mailbox_literal_put": True}
            if name == "try_put":
                return {"kind": "Empty", "span": node_span(sm, s),
                        "mailbox_literal_try_put": True}
            if name == "num":
                return {"kind": "Empty", "span": node_span(sm, s),
                        "mailbox_literal_num_statement": mailbox_get["count"]}
            if name == "try_get":
                if not mailbox_get.get("success", False):
                    return {"kind": "Empty", "span": node_span(sm, s),
                            "mailbox_literal_try_get": True}
                return {"kind": "BlockingAssign", "span": node_span(sm, s),
                        "target": mailbox_get["target"],
                        "value": mailbox_get["value"],
                        "mailbox_literal_try_get": True}
            return {"kind": "BlockingAssign", "span": node_span(sm, s),
                    "target": mailbox_get["target"],
                    "value": mailbox_get["value"],
                    "mailbox_literal_get": True}
        mailbox_sequence = _mailbox_literal_sequence(e)
        if mailbox_sequence is not None:
            if name == "put":
                return {"kind": "Empty", "span": node_span(sm, s),
                        "mailbox_literal_put": True}
            if name == "num":
                return {"kind": "Empty", "span": node_span(sm, s),
                        "mailbox_literal_num_statement": mailbox_sequence}
        if _mailbox_empty_num_method(e):
            return {"kind": "Empty", "span": node_span(sm, s),
                    "mailbox_empty_num": True}
        # A zero-argument task/function with an actually empty body has no
        # state, timing, or diagnostic effect.  In statement position its
        # discarded result is unobservable, so erase this narrow call while
        # leaving every nonempty/defaulted/argumented subroutine loud.
        subroutine = getattr(e, "subroutine", None)
        try:
            args = list(e.arguments)
            body = getattr(subroutine, "body", None)
            body_list = (list(body.list)
                         if type(body).__name__ == "StatementList" else None)
            formal_args = list(getattr(subroutine, "arguments", []))
            kind = str(getattr(subroutine, "subroutineKind", "")).split(".")[-1]
        except Exception:
            args, body_list, formal_args, kind = None, None, None, None
        if (subroutine is not None and args == [] and formal_args == []
                and body_list == [] and kind in ("Task", "Function")):
            return {"kind": "Empty", "span": node_span(sm, s),
                    "empty_subroutine_call": name}
        # A zero-argument function whose complete body is one integral literal
        # return is equally effect-free when the result is discarded.  Reuse
        # the expression-position recognizer so statement and value calls
        # share exactly the same narrow literal boundary.
        if (_SYM is None and subroutine is not None and kind == "Function"
                and _literal_function_call(e)):
            return {"kind": "Empty", "span": node_span(sm, s),
                    "literal_function_statement": name}
    if is_sys and _dynamic_array_literal_size_method(e):
        return {"kind": "Empty", "span": node_span(sm, s),
                "dynamic_array_literal_size": True}
    if is_sys and _zero_size_method(e):
        # Untouched queues/dynamic arrays have size zero, and an untouched
        # empty string has length zero.  Reuse the value converter's source
        # history and receiver checks before erasing the discarded scalar;
        # mutation, aliases, and value-position observations remain loud.
        value = _convert_zero_size_method(sm, e)
        if value.get("kind") != "Unsupported":
            return {"kind": "Empty", "span": node_span(sm, s),
                    "zero_size_statement": name}
    if is_sys:
        # Literal-backed string queries are pure scalar observations. Reuse
        # each value-position converter so ASCII history, argument, width,
        # and range checks remain identical before erasing the discarded
        # result; dynamic strings and effectful uses stay loud.
        string_query_converters = (
            (_string_literal_getc_method, _convert_string_literal_getc),
            (_string_literal_compare_method, _convert_string_literal_compare),
            (_string_literal_atoi_method, _convert_string_literal_atoi),
            (_string_literal_radix_method, _convert_string_literal_radix),
            (_string_literal_len_method, _convert_string_literal_len_method),
        )
        for recognizes, convert in string_query_converters:
            if recognizes(e):
                value = convert(sm, e)
                if value.get("kind") != "Unsupported":
                    return {"kind": "Empty", "span": node_span(sm, s),
                            "string_query_statement": name}
                break
        if _SYM is None and _string_literal_case_method(e):
            # Case conversion allocates a string value that is discarded here;
            # source-pure ASCII history is the only represented fact needed.
            return {"kind": "Empty", "span": node_span(sm, s),
                    "string_case_statement": name}
        if _SYM is None and _string_literal_substr_method(e):
            # ``substr`` has no observable effect in statement position once
            # the receiver and both inclusive bounds are source-pure literals.
            return {"kind": "Empty", "span": node_span(sm, s),
                    "string_substr_statement": name}
        if _floating_string_atoreal_call(e):
            # A proven ASCII literal has no represented real storage.  Its
            # opaque `atoreal` result is therefore inert when discarded; the
            # existing history helper keeps dynamic and effectful strings
            # outside this boundary.
            return {"kind": "Empty", "span": node_span(sm, s),
                    "floating_string_atoreal_statement": name}
    if is_sys and _event_triggered_false(e):
        # Before any trigger, an untouched event's one-bit ``triggered`` query
        # is exactly false. Reuse the value converter's event-history check
        # before erasing the discarded result; triggered or dynamic events
        # remain loud.
        value = _convert_event_triggered_false(sm, e)
        if value.get("kind") != "Unsupported":
            return {"kind": "Empty", "span": node_span(sm, s),
                    "event_triggered_statement": name}
    if is_sys and _associative_empty_query(e):
        # An untouched 2-state associative array has an exact zero element
        # count.  Reuse the value converter's source-order and type checks
        # before erasing a discarded ``num``/``size`` result; populated,
        # aliased, and dynamic arrays remain on the ordinary call boundary.
        value = _convert_associative_empty_query(sm, e)
        if value.get("kind") != "Unsupported":
            return {"kind": "Empty", "span": node_span(sm, s),
                    "associative_empty_query_statement": name}
    if is_sys and _associative_empty_delete_method(e):
        # Deleting an absent key, or all keys from an untouched empty
        # associative array, has no represented state effect.  The helper
        # checks source-pure keys and keeps later count queries exact.
        return {"kind": "Empty", "span": node_span(sm, s),
                "associative_empty_delete_statement": True}
    if is_sys and _associative_empty_endpoint(e):
        # On an untouched associative array, ``first``/``last`` return zero
        # without selecting an element.  The existing converter checks the
        # direct named index argument and empty-array source history before
        # erasing this discarded result; populated and effectful forms stay
        # loud.
        value = _convert_associative_empty_endpoint(sm, e)
        if value.get("kind") != "Unsupported":
            return {"kind": "Empty", "span": node_span(sm, s),
                    "associative_empty_endpoint_statement": name}
    if is_sys and name == "$system":
        # IEEE 1800-2023 §20.17.1: the no-argument task form calls
        # system(NULL) and discards its status.  The self-check state has no
        # host-process or diagnostic channel, so this exact form is inert;
        # commands with a string argument retain the external-effect wall.
        try:
            if not list(e.arguments):
                return {"kind": "Empty", "span": node_span(sm, s),
                        "system_null_task": True}
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
    if is_sys and _coverage_call(e):
        # With no coverage database or registered covergroup in this tier,
        # the literal query returns SV_COV_NOCOV.  In statement position its
        # result is discarded and the call has no represented state effect.
        return {"kind": "Empty", "span": node_span(sm, s),
                "coverage_nocov_statement": True}
    if is_sys and _fseek_stdout_error_call(e):
        # A discarded seek on the predefined stdout descriptor reports its
        # deterministic file-positioning error but changes no represented
        # state.
        return {"kind": "Empty", "span": node_span(sm, s),
                "fseek_stdout_error_statement": True}
    if is_sys and _ftell_stdout_error_call(e):
        # A discarded position query on the predefined stdout descriptor has
        # no represented state effect after reporting its deterministic error.
        return {"kind": "Empty", "span": node_span(sm, s),
                "ftell_stdout_error_statement": True}
    if is_sys and name == "$typename":
        # IEEE 1800-2023 §20.6.1 determines a type without evaluating the
        # expression. A valid one-argument call with a discarded result is
        # therefore inert even when its argument would otherwise be loud.
        try:
            if not getattr(e, "bad", False) and len(e.arguments) == 1:
                return {"kind": "Empty", "span": node_span(sm, s),
                        "typename_statement": True}
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
    if is_sys and name == "$bits":
        # IEEE 1800-2023 §20.6.2 determines bit-stream size without evaluating
        # the expression. A valid discarded query has no represented effect.
        try:
            if not getattr(e, "bad", False) and len(e.arguments) == 1:
                return {"kind": "Empty", "span": node_span(sm, s),
                        "bits_statement": True}
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
    if is_sys and _bit_query_call(e):
        # Literal bit queries are pure and their discarded result is
        # unobservable. Dynamic operands remain ordinary calls because the
        # query must evaluate them before producing its result.
        try:
            args = list(e.arguments)
            if args and all(_integral_literal_source(argument) for argument in args):
                return {"kind": "Empty", "span": node_span(sm, s),
                        "bit_query_statement": name}
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
    if is_sys and _dimension_query_call(e):
        # Fixed dimension queries read only elaborated type metadata.  A
        # discarded result therefore has no represented state effect, while
        # dynamic arrays, selectors, and effectful operands remain loud via
        # the existing value-position converter.
        value = _convert_dimension_query(sm, e)
        if value.get("kind") != "Unsupported":
            return {"kind": "Empty", "span": node_span(sm, s),
                    "dimension_query_statement": name}
    if is_sys and (_time_call(e) or _stime_call(e)):
        # At the time-zero self-check boundary, zero-argument integer time
        # queries are exact zero literals. A discarded result has no state
        # effect; argumented and delayed forms remain on the time boundary.
        return {"kind": "Empty", "span": node_span(sm, s),
                "time_query_statement": name}
    if is_sys and _realtime_call(e):
        # A zero-argument real-time query at the time-zero boundary is an
        # unobserved zero value when used as a statement. The real value is
        # intentionally not represented; argumented and value forms stay
        # loud through the existing real/time boundary.
        return {"kind": "Empty", "span": node_span(sm, s),
                "realtime_query_statement": name}
    if is_sys and _isunbounded_call(e):
        # A bounded literal or parameter is never the special ``$`` value.
        # Its one-bit result is pure and discarded here; ordinary variables,
        # unbounded parameters, and value-position calls stay on the existing
        # expression boundary.
        return {"kind": "Empty", "span": node_span(sm, s),
                "isunbounded_statement": name}
    if is_sys and _clog2_call(e):
        # An admitted ``$clog2`` query has no represented state effect when
        # its result is discarded. Require the existing converter to accept
        # the operand so malformed or effectful forms remain on their normal
        # call boundary.
        value = _convert_clog2(sm, e)
        if value.get("kind") != "Unsupported":
            return {"kind": "Empty", "span": node_span(sm, s),
                    "clog2_statement": name}
    if is_sys and _signing_call(e):
        # A valid integral signing cast is pure. Reuse the expression
        # converter's arity, width, and operand checks before erasing its
        # discarded result; effectful and unsupported operands stay loud.
        value = _convert_signing_call(sm, e)
        if value.get("kind") != "Unsupported":
            return {"kind": "Empty", "span": node_span(sm, s),
                    "signing_statement": name}
    if is_sys and _time_scale_call(e):
        # Time-scale queries read only the literal compilation-unit metadata.
        # Reuse the existing converter so a missing or malformed directive
        # remains loud before erasing the discarded signed exponent.
        value = _convert_time_scale_call(sm, e)
        if value is not None:
            return {"kind": "Empty", "span": node_span(sm, s),
                    "time_scale_statement": name}
    if is_sys and _fopen_invalid_mode_call(e):
        # IEEE 1800-2023 §21.3.1 rejects an invalid literal mode before any
        # file operation.  In statement position the specified zero return
        # value is discarded, so erase only after the expression converter
        # has confirmed the path, mode, width, and literal boundary.
        value = _convert_fopen_invalid_mode(sm, e)
        if value.get("kind") != "Unsupported":
            return {"kind": "Empty", "span": node_span(sm, s),
                    "fopen_invalid_mode_statement": name}
    if is_sys and name in SYSCALL_PURE_DIAGNOSTIC:
        try:
            args = list(e.arguments)
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        if name == "$printtimescale" and args:
            if len(args) != 1:
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
            scope = args[0]
            symbol = getattr(scope, "symbol", None)
            kind = str(getattr(symbol, "kind", "")).split(".")[-1]
            if (type(scope).__name__ != "ArbitrarySymbolExpression"
                    or getattr(scope, "bad", False)
                    or kind not in ("CompilationUnit", "Root", "Instance")):
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
            return {"kind": "Empty", "span": node_span(sm, s),
                    "pure_diagnostic": name}
        if not args:
            return {"kind": "Empty", "span": node_span(sm, s),
                    "pure_diagnostic": name}
    if is_sys and _itor_literal_call(e):
        # `$itor` is a pure integer-to-real conversion. With its result
        # discarded, a direct literal conversion has no modeled state effect;
        # keep dynamic and computed operands on the ordinary loud boundary.
        return {"kind": "Empty", "span": node_span(sm, s),
                "itor_literal_statement": True}
    if is_sys and _bitstoreal_literal_call(e):
        # `$bitstoreal` only produces an opaque real value. With a known
        # literal bit pattern and a discarded result, it has no modeled state
        # effect; dynamic or unknown patterns remain loud.
        return {"kind": "Empty", "span": node_span(sm, s),
                "bitstoreal_literal_statement": True}
    if is_sys and _bitstoshortreal_literal_call(e):
        # `$bitstoshortreal` is the single-precision counterpart: a known
        # literal pattern with a discarded result has no modeled state effect.
        return {"kind": "Empty", "span": node_span(sm, s),
                "bitstoshortreal_literal_statement": True}
    if is_sys and _rtoi_literal_call(e):
        # `$rtoi` is a pure conversion in statement position when its result
        # is discarded.  The value-position converter above is deliberately
        # reused so the literal/range boundary cannot drift between forms.
        return {"kind": "Empty", "span": node_span(sm, s),
                "rtoi_literal_statement": True}
    if is_sys and _realtobits_literal_call(e):
        return {"kind": "Empty", "span": node_span(sm, s),
                "realtobits_literal_statement": True}
    if is_sys and _shortrealtobits_literal_call(e):
        return {"kind": "Empty", "span": node_span(sm, s),
                "shortrealtobits_literal_statement": True}
    if is_sys and name in SYSCALL_ASSERT_CTRL:
        try:
            args = list(e.arguments)
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        if not args:
            return {"kind": "Empty", "span": node_span(sm, s),
                    "pure_diagnostic": name}
        # `$assertcontrol` changes only assertion reporting state. The
        # self-check tier carries no assertion-control register, so its
        # one-literal control form is inert; dynamic and extended forms stay
        # loud until that state is represented.
        if (name == "$assertcontrol" and all(
                _integral_literal_source(argument) for argument in args)):
            return {"kind": "Empty", "span": node_span(sm, s),
                    "pure_diagnostic": name}
    if is_sys and name in SYSCALL_MONITOR_CTRL:
        try:
            args = list(e.arguments)
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        if args:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if re.search(r"\$monitor\s*\(", source):
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        return {"kind": "Empty", "span": node_span(sm, s),
                "pure_diagnostic": name}
    if is_sys and name == SYSCALL_SDF:
        try:
            args = list(e.arguments)
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        # IEEE 32.3 requires the first argument.  The one-argument spelling
        # has no modeled timing state to update; the two-argument spelling is
        # likewise inert only for a static module scope.  The three-argument
        # spelling is inert when its config_file is the specified empty
        # string; retain static scope checks so dynamic hierarchy and every
        # timing-bearing form remain loud.
        filename_only = (len(args) == 1
                         and type(args[0]).__name__ == "StringLiteral")
        static_scope = False
        if len(args) == 2:
            scope = args[1]
            symbol = getattr(scope, "symbol", None)
            scope_kind = str(getattr(symbol, "kind", "")).split(".")[-1]
            static_scope = (
                type(args[0]).__name__ == "StringLiteral"
                and type(scope).__name__ == "ArbitrarySymbolExpression"
                and not getattr(scope, "bad", False)
                and scope_kind in ("Instance", "CompilationUnit", "Root"))
        empty_config = False
        if len(args) == 3:
            scope = args[1]
            symbol = getattr(scope, "symbol", None)
            scope_kind = str(getattr(symbol, "kind", "")).split(".")[-1]
            empty_config = (
                type(args[0]).__name__ == "StringLiteral"
                and type(scope).__name__ == "ArbitrarySymbolExpression"
                and not getattr(scope, "bad", False)
                and scope_kind in ("Instance", "CompilationUnit", "Root")
                and type(args[2]).__name__ == "StringLiteral"
                and args[2].value == ""
            )
        if filename_only or static_scope or empty_config:
            return {"kind": "Empty", "span": node_span(sm, s),
                    "pure_diagnostic": name}
    if is_sys and name == SYSCALL_TIMEFORMAT:
        try:
            args = list(e.arguments)
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        # `$timeformat` only affects later `%t` rendering.  The self-check
        # surface has no time-format renderer, so a call with four literal
        # arguments is inert when this source has no `%t` consumer.  Keep any
        # dynamic argument or possible consumer loud rather than dropping a
        # setting that could change observable output.
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        suffix_literal = (
            len(args) == 4 and
            (type(args[2]).__name__ == "StringLiteral"
             or (type(args[2]).__name__ == "ConversionExpression"
                 and type(getattr(args[2], "operand", None)).__name__ ==
                 "StringLiteral"))
        )
        literal_shape = (
            len(args) == 4
            and type(args[0]).__name__ in ("IntegerLiteral", "UnaryExpression")
            and type(args[1]).__name__ == "IntegerLiteral"
            and suffix_literal
            and type(args[3]).__name__ == "IntegerLiteral"
            and not getattr(args[0], "bad", False)
            and not any(getattr(arg, "bad", False) for arg in args[1:])
        )
        if literal_shape and not re.search(r"%t", source):
            return {"kind": "Empty", "span": node_span(sm, s),
                    "pure_diagnostic": name}
    if is_sys and name == SYSCALL_STROBE:
        try:
            args = list(e.arguments)
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        if not args:
            return {"kind": "SysCall", "span": node_span(sm, s),
                    "name": name, "format": None, "args": [],
                    "arg_signed": []}
        first = args[0]
        if type(first).__name__ != "StringLiteral":
            return unsupported(sm, s, "CallExpression:format")
        converted = [convert_expr(sm, arg) for arg in args[1:]]
        if any(value is None or value.get("kind") == "Unsupported"
               or not _case_expression_ok(value)
               for value in converted):
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        signed = []
        for arg in args[1:]:
            try:
                signed.append(bool(arg.type.isSigned))
            except Exception:
                signed.append(True)
        return {"kind": "SysCall", "span": node_span(sm, s),
                "name": name, "format": first.value, "args": converted,
                "arg_signed": signed}
    if is_sys and name in SYSCALL_FILE_FMT:
        try:
            args = list(e.arguments)
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        if len(args) < 2:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        fd = convert_expr(sm, args[0])
        if fd is not None and fd.get("kind") == "Literal":
            bits = fd.get("bits", "")
            if not bits or any(bit not in "01" for bit in bits):
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
            fd_value = int(bits, 2)
        else:
            fd_value = _stdout_descriptor_variable(sm, args[0])
            if fd_value is None:
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
        if fd_value not in (1, 0x80000001):
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        first = args[1]
        if type(first).__name__ != "StringLiteral":
            return unsupported(sm, s, "CallExpression:format")
        converted = [convert_expr(sm, arg) for arg in args[2:]]
        signed = []
        for arg, value in zip(args[2:], converted):
            if value is None or value.get("kind") == "Unsupported":
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
            try:
                signed.append(bool(arg.type.isSigned))
            except Exception:
                signed.append(True)
        return {"kind": "SysCall", "span": node_span(sm, s),
                "name": "$display" if name == "$fdisplay" else "$write",
                "format": first.value,
                "args": converted, "arg_signed": signed,
                "stdout_file_descriptor": fd_value}
    if is_sys and name in SYSCALL_VCD:
        try:
            args = list(e.arguments)
        except Exception:
            return unsupported(sm, s, "ExpressionStatement:CallExpression")
        if name in ("$dumpon", "$dumpoff", "$dumpall", "$dumpflush"):
            if args:
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
        elif name == "$dumplimit":
            converted = convert_expr(sm, args[0]) if len(args) == 1 else None
            if (converted is None or converted.get("kind") != "Literal"):
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
        elif name == "$dumpfile":
            converted = convert_expr(sm, args[0]) if args else None
            literal_arg = (args and
                           (type(args[0]).__name__ == "StringLiteral" or
                            (type(args[0]).__name__ == "ConversionExpression" and
                             type(getattr(args[0], "operand", None)).__name__ ==
                             "StringLiteral")))
            if len(args) > 1 or (args and
                                 (not literal_arg or converted is None)):
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
        # `$dumpvars` arguments are elaborated scope metadata rather than
        # evaluated expressions; the self-check state has no VCD stream.
        return {"kind": "Empty", "span": node_span(sm, s),
                "pure_diagnostic": name}
    if not is_sys or name not in SYSCALL_FMT + SYSCALL_CTRL:
        if is_sys and name == SYSCALL_FATAL:
            try:
                args = list(e.arguments)
            except Exception:
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
            converted = [convert_expr(sm, arg) for arg in args]
            if all(node is not None and node.get("kind") != "Unsupported"
                   for node in converted):
                # `$fatal` terminates the simulation after evaluating its
                # severity and optional format arguments.  The self-check
                # state has no diagnostic stream, so reuse the existing
                # whole-run halt while retaining the pure argument nodes.
                signed = []
                for arg in args:
                    try:
                        signed.append(bool(arg.type.isSigned))
                    except Exception:
                        signed.append(True)
                return {"kind": "SysCall", "span": node_span(sm, s),
                        "name": "$finish", "format": None,
                        "args": converted, "arg_signed": signed,
                        "fatal_task": True}
        if is_sys and name in SYSCALL_QUIET:
            try:
                args = list(e.arguments)
            except Exception:
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
            # Severity tasks report a diagnostic but do not alter the
            # self-check state. Keep the format literal while evaluating the
            # ordinary pure expressions used as display-style arguments.
            if not args or type(args[0]).__name__ != "StringLiteral":
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
            converted = [convert_expr(sm, arg) for arg in args[1:]]
            if any(node is None or node.get("kind") == "Unsupported"
                   for node in converted):
                # Real/shortreal values have no self-check representation, but
                # a source-pure diagnostic argument is still evaluated by
                # IEEE severity tasks.  Since the diagnostic stream is outside
                # the observable state, erase the whole call only after the
                # source-level purity walk proves every argument harmless.
                if all(_severity_argument_source_ok(arg) for arg in args[1:]):
                    return {"kind": "Empty", "span": node_span(sm, s),
                            "severity_task": name,
                            "opaque_arguments": True}
                return unsupported(sm, s, "ExpressionStatement:CallExpression")
            signed = []
            for arg in args[1:]:
                try:
                    signed.append(bool(arg.type.isSigned))
                except Exception:
                    signed.append(True)
            return {"kind": "SysCall", "span": node_span(sm, s),
                    "name": name, "format": args[0].value,
                    "args": converted, "arg_signed": signed}
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


def _resolve_literal_driver_bits(values, resolution="wire"):
    """Resolve fixed literal net drivers one bit at a time (§28.12).

    ``wire`` uses the ordinary strength-free resolution table; ``and`` and
    ``or`` are the corresponding wired-net reductions, where the dominant
    zero or one wins before unknowns are considered.
    """
    if not values or any(not isinstance(value, str) for value in values):
        return None
    width = len(values[0])
    if width <= 0 or any(len(value) != width for value in values):
        return None
    result = []
    for bits in zip(*values):
        active = [bit for bit in bits if bit != "z"]
        if not active:
            result.append("z")
        elif resolution == "and" and "0" in active:
            result.append("0")
        elif resolution == "or" and "1" in active:
            result.append("1")
        elif any(bit == "x" for bit in active):
            result.append("x")
        elif all(bit == active[0] for bit in active):
            result.append(active[0])
        else:
            result.append("x")
    return "".join(result)


def _lower_disjoint_literal_select_drivers(processes):
    """Lower disjoint constant packed-window drivers to time-zero writes.

    A selected literal driver has no future source reevaluation.  When every
    selected driver on a vector is literal and their fixed windows are
    disjoint, each driver is exactly one independent scalar-state write.  Any
    overlap or dynamic peer remains on the continuous-driver boundary, where
    the scheduler and net-resolution rules are still required.
    """
    groups = {}
    for index, process in enumerate(processes):
        if (process.get("kind") != "Assign"
                or not process.get("continuous_literal_source")
                or process.get("continuous_strength")
                or process.get("target", {}).get("kind") != "SelectTarget"):
            continue
        target = process["target"]
        base = target.get("value", {}).get("name")
        window = _symbolic_target_windows(target)
        if not base or window is None or len(window) != 1:
            continue
        groups.setdefault(base, []).append((index, window[0]))
    for base, entries in groups.items():
        # A group with an unmarked selected assignment is dynamic/effectful;
        # do not erase the literal peer while that driver can still change.
        peers = [
            process for process in processes
            if (process.get("kind") == "Assign"
                and process.get("target", {}).get("kind") == "SelectTarget"
                and process.get("target", {}).get("value", {}).get("name") == base)
        ]
        if len(peers) != len(entries):
            continue
        windows = [window for _index, window in entries]
        if any(old_base == new_base and not (
                new_high < old_low or old_high < new_low)
                for position, (old_base, old_low, old_high) in enumerate(windows)
                for new_base, new_low, new_high in windows[position + 1:]):
            continue
        for index, _window in entries:
            process = processes[index]
            processes[index] = {
                "kind": "Initial",
                "span": process.get("span"),
                "body": {
                    "kind": "BlockingAssign",
                    "span": process.get("span"),
                    "target": dict(process["target"]),
                    "value": process["value"],
                    "continuous_selected_constant_lowered": True,
                },
                "continuous_selected_constant_lowered": True,
            }


def _resolve_literal_select_drivers(processes, resolvable_nets):
    """Resolve a fixed literal packed-window driver set per bit.

    Selected windows are represented with their constant low offset and source
    width.  Reconstruct one full net literal in the existing flat storage,
    applying the same four-state table as whole-net resolution.  A dynamic
    peer, out-of-range window, or variable destination stays on the live
    continuous-driver boundary.
    """
    groups = {}
    for index, process in enumerate(processes):
        if (process.get("kind") != "Assign"
                or not process.get("continuous_literal_source")
                or process.get("continuous_strength")
                or process.get("target", {}).get("kind") != "SelectTarget"):
            continue
        target = process["target"]
        base = target.get("value", {}).get("name")
        if base not in resolvable_nets:
            continue
        window = _symbolic_target_windows(target)
        value = process.get("value", {})
        if (not base or window is None or len(window) != 1
                or value.get("kind") != "Literal"
                or not isinstance(value.get("bits"), str)):
            continue
        groups.setdefault(base, []).append((index, target, value, window[0]))
    for base, entries in groups.items():
        if len(entries) < 2:
            continue
        peers = [
            process for process in processes
            if (process.get("kind") == "Assign"
                and process.get("target", {}).get("kind") == "SelectTarget"
                and process.get("target", {}).get("value", {}).get("name") == base)
        ]
        if len(peers) != len(entries):
            continue
        base_width = entries[0][1].get("value", {}).get("width")
        if (not isinstance(base_width, int) or base_width <= 0
                or any(target.get("value", {}).get("width") != base_width
                       for _index, target, _value, _window in entries)):
            continue
        drivers = [[] for _ in range(base_width)]
        valid = True
        for _index, target, value, _window in entries:
            width = target.get("width")
            bits = value.get("bits")
            index_bits = target.get("index", {}).get("bits")
            if (not isinstance(width, int) or width <= 0
                    or len(bits) != width
                    or not isinstance(index_bits, str)
                    or any(bit not in "01" for bit in index_bits)):
                valid = False
                break
            position = int(index_bits, 2)
            low = position - width + 1 if target.get("descending") else position
            if low < 0 or low + width > base_width:
                valid = False
                break
            for offset in range(width):
                drivers[low + offset].append(bits[-1 - offset])
        if not valid:
            continue
        resolved = []
        for bits in drivers:
            # Merge one scalar position with the same truth table used by
            # whole-net resolution.
            active = [bit for bit in bits if bit != "z"]
            if not active:
                resolved.append("z")
            elif any(bit == "x" for bit in active):
                resolved.append("x")
            elif all(bit == active[0] for bit in active):
                resolved.append(active[0])
            else:
                resolved.append("x")
        literal = dict(entries[0][2])
        literal["width"] = base_width
        literal["bits"] = "".join(reversed(resolved))
        first = entries[0][0]
        process = processes[first]
        target = {"kind": "Ident", "span": process["target"].get("span"),
                  "width": base_width, "name": base}
        processes[first] = {
            "kind": "Initial",
            "span": process.get("span"),
            "body": {
                "kind": "BlockingAssign",
                "span": process.get("span"),
                "target": target,
                "value": literal,
                "continuous_selected_static_resolution": True,
            },
            "continuous_selected_static_resolution": True,
        }
        for index, _target, _value, _window in entries[1:]:
            processes[index] = {
                "kind": "Initial",
                "span": processes[index].get("span"),
                "body": {"kind": "Empty",
                         "span": processes[index].get("span")},
                "continuous_selected_static_resolution": True,
            }


def _reject_overlapping_symbolic_drivers(processes, resolvable_nets=None):
    """Resolve fixed literal legacy net drivers; reject other overlaps."""
    _resolve_literal_select_drivers(processes, resolvable_nets or set())
    _lower_disjoint_literal_select_drivers(processes)
    if _SYM is None and resolvable_nets:
        groups = {}
        for index, process in enumerate(processes):
            if (process.get("kind") != "Assign"
                    or not process.get("continuous_literal_source")
                    or process.get("target", {}).get("kind") != "Ident"):
                continue
            target = process["target"].get("name")
            if target in resolvable_nets:
                groups.setdefault(target, []).append(index)
        for target, indices in groups.items():
            if len(indices) < 2:
                continue
            if any(processes[index].get("continuous_strength")
                   for index in indices):
                continue
            values = [processes[index]["value"].get("bits") for index in indices]
            resolutions = {
                process.get("continuous_resolution", "wire")
                for process in (processes[index] for index in indices)}
            if len(resolutions) != 1:
                continue
            resolved = _resolve_literal_driver_bits(
                values, resolutions.pop())
            if resolved is None:
                continue
            first = indices[0]
            process = processes[first]
            literal = dict(processes[first]["value"])
            literal["bits"] = resolved
            processes[first] = {
                "kind": "Initial",
                "span": process.get("span"),
                "body": {
                    "kind": "BlockingAssign",
                    "span": process.get("span"),
                    "target": dict(process["target"]),
                    "value": literal,
                    "continuous_static_resolution": True,
                },
                "continuous_static_resolution": True,
            }
            for index in indices[1:]:
                # Keep the process list in the self-check vocabulary while
                # removing the already-folded driver from execution.
                processes[index] = {
                    "kind": "Initial",
                    "span": processes[index].get("span"),
                    "body": {"kind": "Empty",
                             "span": processes[index].get("span")},
                    "continuous_static_resolution": True,
                }
    windows = []
    for index, process in enumerate(processes):
        if (process.get("kind") != "Assign"
                or process.get("continuous_strength")):
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


def _lower_multiple_variable_drivers(processes, decls):
    """Erase elaboration-invalid multiple continuous drivers of variables.

    IEEE 1800-2023 §10.3.2 permits at most one continuous assignment to a
    variable.  The self-check state has no diagnostic process for this
    compile-time error, so an invalid group contributes no executable writes.
    Nets retain the ordinary literal-resolution and overlap handling above.
    """
    if _SYM is not None:
        return
    variable_names = {
        declaration.get("name") for declaration in decls
        if declaration.get("kind") == "Var"
    }
    groups = {}
    for index, process in enumerate(processes):
        if process.get("kind") != "Assign":
            continue
        target = process.get("target", {})
        if target.get("kind") != "Ident":
            continue
        name = target.get("name")
        if name in variable_names:
            groups.setdefault(name, []).append(index)
    for name, indices in groups.items():
        if len(indices) < 2:
            continue
        for index in indices:
            process = processes[index]
            processes[index] = {
                "kind": "Initial",
                "span": process.get("span"),
                "body": {"kind": "Empty", "span": process.get("span")},
                "multiple_variable_continuous_drivers_rejected": True,
            }


def _continuous_assignment_has_strength(m):
    """Whether this assignment has an explicit ``(strength1,strength0)``."""
    try:
        if not _SOURCE_BYTES:
            return False
        start = m.syntax.sourceRange.start.offset
        source = _SOURCE_BYTES.decode("utf-8", errors="replace")
        prefix = source[max(0, start - 256):start]
        marker = prefix.rfind("assign")
        return marker >= 0 and re.match(r"\s*\(", prefix[marker + len("assign"):]) is not None
    except Exception:
        return False


def _dynamic_array_continuous_target(expression):
    """Whether a continuous assignment selects an element of a dynamic array.

    IEEE 1800-2023 §6.21 rejects this target at elaboration: dynamic-array
    elements may only be written procedurally.  The self-check tier has no
    diagnostic process, so the rejected assignment can be represented by an
    inert initial process while the surrounding self-check body remains live.
    """
    try:
        if type(expression).__name__ != "ElementSelectExpression":
            return False
        base = getattr(expression, "value", None)
        symbol = getattr(base, "symbol", None)
        symbol_type = getattr(symbol, "type", None)
        canonical = getattr(symbol_type, "canonicalType", symbol_type)
        return type(canonical).__name__ == "DynamicArrayType"
    except Exception:
        return False


def convert_continuous_assign(sm, m):
    if getattr(m, "delay", None) is not None:
        return unsupported(sm, m, "ContinuousAssignSymbol:delay")
    e = m.assignment
    explicit_strength = _continuous_assignment_has_strength(m)
    if type(e).__name__ != "AssignmentExpression":
        return unsupported(sm, m, "ContinuousAssignSymbol:" + type(e).__name__)
    left_symbol = getattr(e.left, "symbol", None)
    if left_symbol is None:
        left_symbol = getattr(getattr(e.left, "value", None), "symbol", None)
    net_kind = str(getattr(getattr(left_symbol, "netType", None),
                           "netKind", "")).split(".")[-1]
    continuous_resolution = (
        "and" if net_kind in ("WAnd", "TriAnd") else
        "or" if net_kind in ("WOr", "TriOr") else None)
    if e.op is not None or e.timingControl is not None or e.isNonBlocking:
        return unsupported(sm, m, "ContinuousAssignSymbol:form")
    if _dynamic_array_continuous_target(e.left):
        # §6.21: a dynamic-array element is not a legal continuous-assignment
        # destination.  There is no runtime write to model after elaboration
        # rejects the statement, so keep the process inert and retain the
        # surrounding initial self-check program.
        return {
            "kind": "Initial",
            "span": node_span(sm, e),
            "body": {"kind": "Empty", "span": node_span(sm, e)},
            "dynamic_array_continuous_target_rejected": True,
        }
    streaming = type(e.left).__name__ == "StreamingConcatenationExpression"
    legacy_streaming = _SYM is None and streaming
    symbolic_streaming = _SYM is not None and streaming
    bound_literal = None
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
        bound_literal = (_continuous_bound_literal(sm, e.right)
                         if _SYM is None else None)
        if bound_literal is None and _SYM is None:
            bound_literal = _continuous_static_value(sm, e.right)
        if bound_literal is None and _SYM is None:
            bound_literal = _constant_integral_source(sm, e.right)
        if bound_literal is not None:
            value = bound_literal
    # A single explicitly strengthened whole-net literal is value-equivalent
    # to the ordinary flat driver. Selected strength forms are kept loud until
    # the target representation carries per-window strength metadata.
    if explicit_strength and target.get("kind") not in ("Ident", "SelectTarget"):
        return unsupported(sm, m, "AssignmentExpression:target")
    # A fixed-unpacked variable cell has already been expanded into the flat
    # self-check storage by ``_fixed_array_cell``.  When its continuous source
    # is a literal, the assignment has no future reevaluation and needs no
    # driver resolution: one time-zero blocking write is the exact value seen
    # by the initial-only runner.  Keep net arrays and every dynamic or
    # multiply-driven cell on the scheduler-owned continuous boundary.
    if (_SYM is None and type(e.left).__name__ == "ElementSelectExpression"
            and getattr(left_symbol, "kind", None) is not None
            and str(left_symbol.kind) in ("SymbolKind.Variable", "SymbolKind.Net")
            and target.get("kind") == "Ident"
            and value is not None and value.get("kind") == "Literal"
            and (_integral_literal_source(e.right) or bound_literal is not None)):
        cell = _fixed_array_cell(sm, e.left)
        if cell is not None:
            cell_name = target.get("name", "")
            source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
            assignments = re.findall(
                r"(?m)\bassign\s+(?:\([^)]*\)\s*)?" +
                re.escape(cell_name) + r"\s*=", source)
            if len(assignments) == 1:
                return {
                    "kind": "Initial",
                    "span": node_span(sm, e),
                    "body": {
                        "kind": "BlockingAssign",
                        "span": node_span(sm, e),
                        "target": target,
                        "value": value,
                        "continuous_array_cell_lowered": True,
                    },
                    "continuous_array_cell_lowered": True,
                    "continuous_strength": explicit_strength,
                }
    if (_SYM is None and type(e.left).__name__ in (
            "NamedValueExpression", "ElementSelectExpression",
            "RangeSelectExpression")
            and getattr(left_symbol, "kind", None) is not None
            and str(left_symbol.kind) in ("SymbolKind.Net", "SymbolKind.Variable")
            and value is not None and value.get("kind") == "Literal"
            and (_integral_literal_source(e.right) or bound_literal is not None)):
        # A single whole-net or constant packed-window literal driver has no
        # future re-evaluation and no resolution choice. At time zero it is
        # exactly the existing flat state assignment. Keep every other
        # continuous form on the scheduler-owned boundary, including multiple
        # drivers and dynamic or aggregate targets.
        name = getattr(left_symbol, "name", "")
        source = _SOURCE_BYTES.decode("utf-8", errors="replace") if _SOURCE_BYTES else ""
        if target.get("kind") == "Ident":
            driver_pattern = (r"(?m)\bassign\s+(?:\([^)]*\)\s*)?" + re.escape(name)
                              + r"\s*=")
        elif target.get("kind") == "SelectTarget":
            driver_pattern = (r"(?m)\bassign\s+(?:\([^)]*\)\s*)?" + re.escape(name)
                              + r"\s*\[")
        else:
            driver_pattern = None
        assignments = (re.findall(driver_pattern, source)
                       if driver_pattern is not None else [])
        if len(assignments) == 1 and target.get("kind") in (
                "Ident", "SelectTarget"):
            return {
                "kind": "Initial",
                "span": node_span(sm, e),
                "body": {
                    "kind": "BlockingAssign",
                    "span": node_span(sm, e),
                    "target": target,
                    "value": value,
                    "continuous_constant_lowered": True,
                    "continuous_strength": explicit_strength,
                },
                "continuous_constant_lowered": True,
                "continuous_strength": explicit_strength,
            }
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
    result = {
        "kind": "Assign",
        "span": node_span(sm, e),
        "target": target,
        "value": value,
    }
    if (_SYM is None and target.get("kind") in ("Ident", "SelectTarget")
            and (_integral_literal_source(e.right) or bound_literal is not None)):
        result["continuous_literal_source"] = True
        result["continuous_strength"] = explicit_strength
        if continuous_resolution is not None:
            result["continuous_resolution"] = continuous_resolution
    return result


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
    union_decls = _unpacked_union_decls(sm, m)
    if union_decls is not None:
        return union_decls
    assoc_decls = _finite_string_assoc_decls(sm, m)
    if assoc_decls is not None:
        return assoc_decls
    assoc_decls = _finite_integral_assoc_decls(sm, m)
    if assoc_decls is not None:
        return assoc_decls
    array_decls = convert_fixed_array_vars(sm, m)
    if array_decls is not None:
        return array_decls
    if _SYM is None and is_inert_2state_queue_decl(m):
        return {"kind": "Empty", "span": sym_span(sm, m)}
    if _SYM is None and is_inert_2state_dynamic_array_decl(m):
        return {"kind": "Empty", "span": sym_span(sm, m)}
    if _SYM is None and is_inert_2state_associative_array_decl(m):
        return {"kind": "Empty", "span": sym_span(sm, m)}
    if _SYM is None and is_inert_class_handle_decl(m):
        return {"kind": "Empty", "span": sym_span(sm, m)}
    if _SYM is None and is_literal_semaphore_decl(m):
        return {"kind": "Empty", "span": sym_span(sm, m),
                "opaque_semaphore_literal_new_write": True}
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
        if type(array_type).__name__ == "DynamicArrayType":
            # Keep the dynamic allocation itself out of the flat state, but
            # materialize its sampled constant extent as ordinary cells. An
            # uninitialized or later-resized dynamic array has no fixed shape
            # that this representation could soundly provide. Four-state
            # arrays are equally representable: their cells start at x,
            # while the existing two-state branch below still starts at 0.
            count = _dynamic_array_constant_extent(m)
            if count is None:
                return None
            element_type = array_type.elementType
            element_leaf = element_type.canonicalType
            nested_shape = _fixed_array_dimensions(element_type, max_cells=1024)
            if nested_shape is not None:
                if getattr(m, "initializer", None) is not None:
                    return None
                inner_dimensions, leaf_type = nested_shape
                width, two, reason = type_width_2s(leaf_type)
                if width is None or reason is not None:
                    return None
                positions = [(position,)
                             for position in range(count)]
                for left, right in inner_dimensions:
                    step = 1 if right >= left else -1
                    positions = [prefix + (position,)
                                 for prefix in positions
                                 for position in range(left, right + step, step)]
                base = _array_storage_name(m)
                return [signed_metadata({
                    "kind": "Var", "span": sym_span(sm, m),
                    "name": base + "".join(f"[{position}]" for position in indexes),
                    "width": width,
                    "init": ({"kind": "Literal", "span": None,
                              "width": width, "bits": "0" * width}
                             if two else None),
                }, leaf_type) for indexes in positions]
            if type(element_leaf).__name__ == "UnpackedStructType":
                # A struct element is represented by one cell per integral
                # field. ``new[N]`` creates N default-valued elements, so
                # apply field initializers independently to each sampled
                # element while retaining the existing aggregate boundaries.
                if getattr(element_leaf, "isTagged", False):
                    return None
                base = _array_storage_name(m)
                declarations = []
                for position in range(count):
                    cell_base = f"{base}[{position}]"
                    cells = _unpacked_struct_oob_defaults(
                        sm, cell_base, element_leaf, sym_span(sm, m))
                    if cells is None:
                        return None
                    for name, width, init, field_type in cells:
                        if init is not None and not field_type.isFourState:
                            init = squash2_wrap(init, width)
                        declarations.append(signed_metadata({
                            "kind": "Var",
                            "span": sym_span(sm, m),
                            "name": name,
                            "width": width,
                            "init": init,
                        }, field_type))
                return declarations
            width, two, reason = type_width_2s(element_type)
            if width is None or reason is not None:
                return None
            base = _array_storage_name(m)
            initializer = getattr(m, "initializer", None)
            values = None
            initializer_shape = initializer
            while type(initializer_shape).__name__ == "ConversionExpression":
                initializer_shape = getattr(initializer_shape, "operand", None)
            if (initializer is not None
                    and type(initializer_shape).__name__ != "NewArrayExpression"):
                values = _fixed_array_initializer_values(
                    sm, initializer, base, width, count)
                if values is None:
                    return None
            return [signed_metadata({
                "kind": "Var",
                "span": sym_span(sm, m),
                "name": f"{base}[{position}]",
                "width": width,
                "init": (squash2_wrap(values[index], width) if two
                          and values is not None and values[index] is not None else
                          values[index] if values is not None else
                          ({"kind": "Literal", "span": None,
                            "width": width, "bits": "0" * width}
                           if two else None)),
            }, element_type) for index, position in enumerate(range(count))]
        if type(array_type).__name__ != "FixedSizeUnpackedArrayType":
            return None
        dimensions_shape = _fixed_array_dimensions(array_type)
        if dimensions_shape is None:
            # The flat state normally expands every leaf, but the standard
            # requires implementations to accept arrays much larger than a
            # practical envelope can enumerate.  For a one-dimensional
            # integral array, retain only constant-index cells that the
            # source actually observes. Dynamic, whole-array, and aggregate
            # uses remain loud rather than receiving a fabricated default.
            full_shape = _fixed_array_dimensions(array_type, max_cells=None)
            if full_shape is None:
                return None
            full_dimensions, full_leaf = full_shape
            if len(full_dimensions) != 1:
                return None
            width, two, reason = type_width_2s(full_leaf)
            if width is None or reason is not None:
                return None
            positions = _fixed_array_constant_uses(m)
            if positions is None:
                return None
            left, right = full_dimensions[0]
            positions = [position for position in positions
                         if min(left, right) <= position <= max(left, right)]
            positions.sort(reverse=right < left)
            decls = []
            for position in positions:
                init = {"kind": "Literal", "span": None,
                        "width": width, "bits": "0" * width} if two else None
                decls.append(signed_metadata({
                    "kind": "Var", "span": sym_span(sm, m),
                    "name": f"{_array_storage_name(m)}[{position}]",
                    "width": width, "init": init,
                }, full_leaf))
            return decls
        dimensions, leaf_type = dimensions_shape
        if type(leaf_type).__name__ == "UnpackedStructType":
            # Compose the existing shallow-struct field cells with the
            # fixed-array cell expansion.  Whole struct values and aggregate
            # array initializers still need an aggregate store, so this slice
            # admits declarations without an initializer only.
            if getattr(leaf_type, "isTagged", False) or getattr(m, "initializer", None) is not None:
                return None
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
                cells = _unpacked_struct_field_cells(
                    cell, leaf_type, sym_span(sm, m))
                if cells is None:
                    return None
                for name, width, init, field_type in cells:
                    declarations.append(signed_metadata({
                        "kind": "Var", "span": sym_span(sm, m),
                        "name": name, "width": width, "init": init,
                    }, field_type))
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


def _net_has_only_literal_continuous_drivers(m):
    """Recognize a ``tri`` net whose complete driver set is literal-only.

    A fixed literal driver has no future reevaluation, so ``tri`` and ``wire``
    have the same four-state value in the flat self-check world.  Keep the
    declaration loud unless every continuous assignment targeting this net is
    in that closed subset; this prevents a dynamic tri driver from slipping
    through merely because the declaration itself is otherwise representable.
    """
    try:
        instance = m.parentScope.containingInstance
        found = False
        valid = True
        strength_drivers = 0
        driver_count = 0

        def inspect(node):
            nonlocal found, valid, strength_drivers, driver_count
            if type(node).__name__ != "ContinuousAssignSymbol":
                return
            assignment = getattr(node, "assignment", None)
            if assignment is None:
                return
            left = getattr(assignment, "left", None)
            symbol = getattr(left, "symbol", None)
            if symbol is None:
                symbol = getattr(getattr(left, "value", None), "symbol", None)
            if symbol is not m:
                return
            found = True
            driver_count += 1
            explicit_strength = _continuous_assignment_has_strength(node)
            if explicit_strength:
                strength_drivers += 1
            valid = (valid and assignment.op is None
                     and assignment.timingControl is None
                     and not assignment.isNonBlocking
                     and (not explicit_strength or driver_count == 1)
                     and _integral_literal_source(assignment.right))

        instance.visit(inspect)
        # A single strengthened literal has the same fixed value as its
        # ordinary four-state driver. Any additional driver would require
        # per-driver strength resolution, so retain the loud tri boundary.
        return (found and valid and
                (strength_drivers == 0 or driver_count == 1))
    except Exception:
        return False


def _wired_net_has_only_literal_drivers(m):
    """Whether a wired net has a closed set of literal continuous drivers."""
    try:
        instance = m.parentScope.containingInstance
        found = False
        valid = True

        def inspect(node):
            nonlocal found, valid
            if type(node).__name__ != "ContinuousAssignSymbol":
                return
            assignment = getattr(node, "assignment", None)
            if assignment is None:
                return
            left = getattr(assignment, "left", None)
            symbol = getattr(left, "symbol", None)
            if symbol is None:
                symbol = getattr(getattr(left, "value", None), "symbol", None)
            if symbol is not m:
                return
            found = True
            valid = (valid and assignment.op is None
                     and assignment.timingControl is None
                     and not assignment.isNonBlocking
                     and not _continuous_assignment_has_strength(node)
                     and _integral_literal_source(assignment.right))

        instance.visit(inspect)
        return found and valid
    except Exception:
        return False


def convert_net(sm, m):
    nk = str(m.netType.netKind).split(".")[-1]
    if nk not in ("Wire", "Tri", "WAnd", "WOr", "TriAnd", "TriOr"):
        return unsupported(sm, m, "NetSymbol:" + nk)
    if nk == "Tri" and not _net_has_only_literal_continuous_drivers(m):
        return unsupported(sm, m, "NetSymbol:Tri")
    resolution = None
    if nk in ("WAnd", "TriAnd", "WOr", "TriOr"):
        if not _wired_net_has_only_literal_drivers(m):
            return unsupported(sm, m, "NetSymbol:" + nk)
        resolution = "and" if nk in ("WAnd", "TriAnd") else "or"
    if getattr(m, "delay", None) is not None:
        return unsupported(sm, m, "NetSymbol:delay")
    # A one-dimensional fixed-unpacked wire array can use the same flat
    # storage as a variable array when each cell is addressed directly.  The
    # cells remain ``Net`` declarations, so the existing literal-driver
    # folding still resolves multiple constant drivers per cell.  Whole,
    # dynamic, multidimensional, and non-integral array uses stay loud at the
    # expression/target boundary.
    array_type = getattr(m.type, "canonicalType", None)
    if type(array_type).__name__ == "FixedSizeUnpackedArrayType":
        element_type = array_type.elementType
        if type(element_type.canonicalType).__name__ != "FixedSizeUnpackedArrayType":
            width, reason = type_width(element_type)
            if width is not None and reason is None:
                left, right = int(array_type.range.left), int(array_type.range.right)
                if abs(left - right) + 1 <= 1024:
                    base = _array_storage_name(m)
                    return [signed_metadata({
                        "kind": "Net",
                        "span": sym_span(sm, m),
                        "name": f"{base}[{position}]",
                        "width": width,
                        "init": None,
                    }, element_type) for position in range(
                        left, right + (1 if right >= left else -1),
                        1 if right >= left else -1)]
    w, reason = type_width(m.type)
    if w is None:
        return unsupported(sm, m, "NetSymbol:" + reason)
    init = m.initializer
    declaration = signed_metadata({
        "kind": "Net",
        "span": sym_span(sm, m),
        "name": _storage_name(m),
        "width": w,
        "init": convert_expr(sm, init) if init is not None else None,
    }, m.type)
    if resolution is not None:
        declaration["continuous_resolution"] = resolution
    return declaration


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
        if (is_chandle_decl(symbol) or is_string_decl(symbol)
                or is_inert_2state_floating_decl(symbol)
                or is_inert_class_handle_decl(symbol)
                or is_literal_semaphore_decl(symbol)):
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
                    if (is_module_event_decl(m) or is_module_floating_decl(m)
                            or is_chandle_decl(m)
                            or is_inert_class_handle_decl(m)
                            or is_literal_semaphore_decl(m)
                            or is_module_virtual_interface_null_decl(m)
                            or is_string_decl(m)
                            or is_inert_2state_queue_decl(m)
                            or is_inert_2state_dynamic_array_decl(m)
                            or is_inert_2state_associative_array_decl(m)):
                        continue
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
                    converted = convert_net(sm, m)
                    if isinstance(converted, list):
                        decls.extend(converted)
                    else:
                        decls.append(converted)
            elif k == "ProceduralBlock":
                processes.append(convert_procedural_block(sm, m))
            elif k == "ContinuousAssign":
                processes.append(convert_continuous_assign(sm, m))
            elif k == "StatementBlock":
                # Scope artifact for statement-level begin/end blocks; its
                # contents appear inside the owning process body.
                continue
            elif k == "Subroutine":
                # Empty subroutines and pure literal-return functions are
                # metadata only.  Calls in statement position are erased by
                # _convert_syscall; effectful signatures and bodies remain
                # loud.
                body = getattr(m, "body", None)
                formal_args = list(getattr(m, "arguments", []))
                body_list = (list(body.list)
                             if type(body).__name__ == "StatementList" else None)
                if (formal_args == [] and body_list == []) or \
                        _literal_function_symbol(m):
                    # The declaration has no runtime node at all; keeping an
                    # Empty in Module.others would make the self-check runner
                    # classify it as a non-initial process.
                    continue
                else:
                    others.append(unsupported(sm, m,
                                              type(m).__name__ + ":" + k))
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
    _lower_multiple_variable_drivers(processes, decls)
    others.extend(_module_storage_collisions(ports, decls, processes, span))
    others.extend(_static_initialization_barriers(sm, decls, ports))

    # Constant continuous windows are storage-only in the legacy runner too;
    # fold only the explicitly resolvable literal wire groups before retaining
    # the loud overlap boundary for every other continuous form.
    resolvable_nets = {
        declaration.get("name") for declaration in decls
        if declaration.get("kind") == "Net"
    }
    _reject_overlapping_symbolic_drivers(processes, resolvable_nets)

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
            or is_bound_enum_member(member)
            or is_module_event_decl(member)
            or is_module_floating_decl(member)
            or is_chandle_decl(member)
            or is_module_virtual_interface_null_decl(member)
            or is_string_decl(member)
            or is_inert_2state_queue_decl(member)
            or is_inert_2state_dynamic_array_decl(member)
            or is_inert_2state_associative_array_decl(member))


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
    global _ASSOC_CELLS
    previous = (_PACKAGE_BINDINGS, _PACKAGE_SCOPES, _ELAB_BINDINGS,
                _ELAB_PARAMETERS, _ELAB_HIER_VALUES, _ELAB_CURRENT_SCOPE,
                _MIN_TYP_MAX, _ASSOC_CELLS)
    _MIN_TYP_MAX = {MinTypMax.Min: "min", MinTypMax.Typ: "typ", MinTypMax.Max: "max"}[
        comp.options.minTypMax]
    _ELAB_BINDINGS, _ELAB_PARAMETERS, _ELAB_HIER_VALUES, _ELAB_CURRENT_SCOPE = {}, set(), set(), ""
    _ASSOC_CELLS = {}
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
         _ELAB_PARAMETERS, _ELAB_HIER_VALUES, _ELAB_CURRENT_SCOPE,
         _MIN_TYP_MAX, _ASSOC_CELLS) = previous


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
    if is_inert_2state_floating_decl(m):
        return {"kind": "Empty", "span": sym_span(sm, m)}
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
        dimensions_shape = _fixed_array_dimensions(array_type)
        if dimensions_shape is not None and len(dimensions_shape[0]) > 1:
            dimensions, leaf_type = dimensions_shape
            width, two, reason = type_width_2s(leaf_type)
            if width is None or reason is not None:
                return None
            if getattr(m, "initializer", None) is not None:
                return None
            dtype, dtype_reason = _dtype_sym(sm, leaf_type, _decl_type_syntax(m))
            if (dtype is not None and dtype_reason is None
                    and dtype.get("kind") == "PackedType"
                    and dtype.get("packed") is None):
                dims = []
                current = leaf_type.canonicalType
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
            positions = [()]
            for left, right in dimensions:
                step = 1 if right >= left else -1
                positions = [prefix + (position,)
                             for prefix in positions
                             for position in range(left, right + step, step)]
            decls = []
            for indexes in positions:
                init = ({"kind": "Literal", "span": None, "width": width,
                         "bits": "0" * width} if two else None)
                decls.append({
                    "kind": "Var", "span": sym_span(sm, m),
                    "name": m.name + "".join(f"[{position}]" for position in indexes),
                    "width": dtype, "init": init,
                })
            return decls
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
