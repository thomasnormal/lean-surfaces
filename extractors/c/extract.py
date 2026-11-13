#!/usr/bin/env python3
"""extract.py — C translation unit -> the c-0.1 envelope (docs/c-envelope-schema.md).

Translation phases 1-6 run OUTSIDE Lean, in clang; Lean owns phase 7.  This
extractor drives `clang -Xclang -ast-dump=json` under the PINNED PROFILE and
lowers clang's AST into the envelope the ingester reads.

    python3 extractors/c/extract.py <file.c> [-o out.json]

THE CONTRACT (identical to the Python and SystemVerilog extractors):

* NEVER fails on valid C.  Any node kind outside the pinned vocabulary
  becomes an `Unsupported` leaf carrying clang's own class name and <=200
  characters of source text.
* Hard errors -- unreadable file, a clang DIAGNOSTIC, a host that does not
  satisfy the profile -- exit NON-ZERO and say why.  A clang diagnostic is
  the sharp one: clang emits a PARTIAL AST alongside it, and censusing a
  program that does not compile is a WRONG answer rather than a smaller one.
  `harness/c_construct_census.py` shipped that bug once; this inherits the
  refusal rather than the bug.
* DETERMINISTIC: same input bytes => same output bytes, double-run verified.
* No absolute paths in the payload; `source_file` is repo-relative and spans
  carry line/column only.

TWO THINGS CLANG'S JSON MAKES US HONEST ABOUT.

1. `type` is a flat `qualType` STRING almost everywhere.  The seven
   structured type kinds appear ONLY under the corpus's 7 `TypedefDecl`s
   (measured: 22 nodes, all of them there).  So the envelope carries the
   string the frontend gives, plus a structured `underlying` tree on
   typedefs.  Parsing qualType into a tree would be writing the C type
   parser the schema exists to avoid.
2. Locations are STICKY: a node omits `file`/`line` when it repeats its
   predecessor's.  The walk carries both forward, and every span is
   resolved against that state.  Without it every span after the first is
   wrong, silently.

Python >= 3.9, stdlib only.
"""

import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys

SCHEMA_VERSION = "c-0.1"
PROFILE_ID = "c-profile-0.1"
PROFILE_FLAGS = ["-std=c23", "-D_FORTIFY_SOURCE=0"]
AST_FLAGS = PROFILE_FLAGS + ["-fsyntax-only", "-Xclang", "-ast-dump=json"]
# The C differential surface has one trusted compiler, including its build
# revision.  A family-only stamp cannot tell two AST producers apart.
PINNED_FRONTEND_VERSION = (
    "clang version 21.1.8 "
    "(https://github.com/conda-forge/clangdev-feedstock "
    "334cf9a5e6c0331e9f261eaf01fc3568724fcce9)"
)
CLANG_ENV = "LEAN_C_CLANG"
STRING_BYTES_PLUGIN_ENV = "LEAN_C_STRING_BYTES_PLUGIN"
FLOATING_BITS_PLUGIN_ENV = "LEAN_C_FLOATING_BITS_PLUGIN"
RECORD_LAYOUT_PLUGIN_ENV = "LEAN_C_RECORD_LAYOUT_PLUGIN"

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

DECLS = {"FunctionDecl", "VarDecl", "ParmVarDecl", "FieldDecl", "RecordDecl",
         "TypedefDecl", "EnumDecl", "EnumConstantDecl", "EmptyDecl"}
STMTS = {"CompoundStmt", "DeclStmt", "IfStmt", "ForStmt", "WhileStmt", "DoStmt",
         "ReturnStmt", "BreakStmt", "ContinueStmt", "GotoStmt", "LabelStmt",
         "NullStmt", "SwitchStmt", "CaseStmt", "DefaultStmt"}
EXPRS = {"IntegerLiteral", "CharacterLiteral", "StringLiteral", "FloatingLiteral",
         "CXXBoolLiteralExpr",
         "ChooseExpr",
         "DeclRefExpr", "MemberExpr", "ArraySubscriptExpr", "CallExpr",
         "BinaryOperator", "CompoundAssignOperator", "UnaryOperator",
         "ConditionalOperator", "ParenExpr", "ImplicitCastExpr", "CStyleCastExpr",
         "InitListExpr", "ImplicitValueInitExpr", "CompoundLiteralExpr", "UnaryExprOrTypeTraitExpr",
         "ConstantExpr", "VAArgExpr"}
TYPES = {"BuiltinType", "PointerType", "RecordType", "TypedefType",
         "ElaboratedType", "ParenType", "FunctionProtoType"}
VOCAB = DECLS | STMTS | EXPRS | TYPES


def canonicalize_ids(tree):
    """Replace clang's process-address node IDs with traversal ordinals.

    clang's JSON uses heap addresses (``0x…``) for ``id`` and for the
    references which point back to a declaration.  Those addresses are not
    part of the source program and change on every compiler invocation.  A
    first-occurrence map preserves identity while making the input to the
    envelope deterministic.  The walk also covers label and declaration
    reference fields, including the nested ``referencedDecl`` records.
    """
    ids = {}

    def canon(value):
        if not isinstance(value, str) or not value.startswith("0x"):
            return value
        if value not in ids:
            ids[value] = "id" + str(len(ids))
        return ids[value]

    def walk(value):
        if isinstance(value, dict):
            for key in list(value):
                item = value[key]
                if (key == "id" or key.endswith("Id")) and isinstance(item, str):
                    value[key] = canon(item)
                else:
                    walk(item)
        elif isinstance(value, list):
            for item in value:
                walk(item)

    walk(tree)
    return tree


def die(msg):
    sys.exit("extract.py: " + msg)


def clang_executable():
    return os.environ.get(CLANG_ENV, "clang")


def frontend_version():
    out = subprocess.run([clang_executable(), "--version"],
                         capture_output=True, text=True)
    first = (out.stdout or "").splitlines()[0] if out.stdout else ""
    if out.returncode != 0 or first != PINNED_FRONTEND_VERSION:
        die("frontend is not pinned to %s; got %s" %
            (PINNED_FRONTEND_VERSION, first or "<no version>"))
    return first


def clang_json(path):
    out = subprocess.run([clang_executable()] + AST_FLAGS + [path],
                         capture_output=True, text=True)
    if out.returncode != 0:
        die("clang rejected %s (exit %d).  A partial AST is a DIFFERENT "
            "program, not a smaller one:\n%s" % (path, out.returncode,
                                                 out.stderr[:2000]))
    if not out.stdout:
        die("clang produced no AST for %s\n%s" % (path, out.stderr[:2000]))
    return json.loads(out.stdout)


def string_byte_records(path):
    """Observe decoded literal bytes through Clang's own AST API.

    The normal extractor remains usable without the optional plugin.  When it
    is supplied, every StringLiteral must be observed and records are joined
    by Clang's source offsets; no spelling is decoded here.
    """
    plugin = os.environ.get(STRING_BYTES_PLUGIN_ENV)
    if not plugin:
        return None
    if not os.path.isfile(plugin):
        die("%s does not name a plugin file" % STRING_BYTES_PLUGIN_ENV)
    command = ([clang_executable()] + PROFILE_FLAGS + ["-fsyntax-only",
               "-Xclang", "-load", "-Xclang", plugin,
               "-Xclang", "-plugin", "-Xclang", "lean-c-string-bytes",
               path])
    out = subprocess.run(command, capture_output=True)
    if out.returncode:
        die("string byte probe rejected %s: %s" %
            (path, out.stderr.decode(errors="replace")[:2000]))
    try:
        records = json.loads(out.stdout.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        die("string byte probe returned invalid JSON: %s" % error)
    if not isinstance(records, list):
        die("string byte probe returned a non-array")
    by_offset = {}
    for record in records:
        if not isinstance(record, dict) or record.get("kind") != "StringLiteral":
            die("string byte probe returned an invalid record")
        offset = record.get("offset")
        bytes_ = record.get("bytes")
        if type(offset) is not int or not isinstance(bytes_, list):
            die("string byte probe returned an invalid offset/bytes record")
        if any(type(byte) is not int or byte < 0 or byte > 255 for byte in bytes_):
            die("string byte probe returned a byte outside 0..255")
        by_offset.setdefault(offset, []).append(record)
    return by_offset


def floating_bit_records(path):
    """Observe Clang's rounded FloatingLiteral bits through its AST API.

    The optional probe is joined by the source offset already present in the
    JSON AST.  The extractor never interprets a C spelling or recomputes a
    floating value; it only validates and carries the frontend observation.
    """
    plugin = os.environ.get(FLOATING_BITS_PLUGIN_ENV)
    if not plugin:
        return None
    if not os.path.isfile(plugin):
        die("%s does not name a plugin file" % FLOATING_BITS_PLUGIN_ENV)
    command = ([clang_executable()] + PROFILE_FLAGS + ["-fsyntax-only",
               "-Xclang", "-load", "-Xclang", plugin,
               "-Xclang", "-plugin", "-Xclang", "lean-c-floating-bits",
               path])
    out = subprocess.run(command, capture_output=True)
    if out.returncode:
        die("floating bits probe rejected %s: %s" %
            (path, out.stderr.decode(errors="replace")[:2000]))
    try:
        records = json.loads(out.stdout.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        die("floating bits probe returned invalid JSON: %s" % error)
    if not isinstance(records, list):
        die("floating bits probe returned a non-array")
    by_offset = {}
    for record in records:
        if not isinstance(record, dict) or record.get("kind") != "FloatingLiteral":
            die("floating bits probe returned an invalid record")
        offset, length, width = (record.get(name) for name in
                                 ("offset", "token_length", "bit_width"))
        bits, typ = record.get("bits_hex"), record.get("type")
        if (type(offset) is not int or offset < 0 or type(length) is not int or
                length <= 0 or type(width) is not int or width <= 0 or
                type(bits) is not str or not bits or
                any(char not in "0123456789abcdefABCDEF" for char in bits) or
                type(typ) is not str or not typ):
            die("floating bits probe returned an invalid record")
        by_offset.setdefault(offset, []).append(record)
    return by_offset


def record_layout_records(path):
    """Observe complete record layouts through Clang's AST API.

    Records are keyed by the parser-provided source offset.  The envelope
    retains line/column spans, so this is the stable join key available in
    the approved AST without decoding a type spelling or inventing an ID.
    """
    plugin = os.environ.get(RECORD_LAYOUT_PLUGIN_ENV)
    if not plugin:
        return None
    if not os.path.isfile(plugin):
        die("%s does not name a plugin file" % RECORD_LAYOUT_PLUGIN_ENV)
    command = ([clang_executable()] + PROFILE_FLAGS + ["-fsyntax-only",
               "-Xclang", "-load", "-Xclang", plugin,
               "-Xclang", "-plugin", "-Xclang", "lean-c-record-layout",
               path])
    out = subprocess.run(command, capture_output=True)
    if out.returncode:
        die("record layout probe rejected %s: %s" %
            (path, out.stderr.decode(errors="replace")[:2000]))
    try:
        records = json.loads(out.stdout.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        die("record layout probe returned invalid JSON: %s" % error)
    if not isinstance(records, list):
        die("record layout probe returned a non-array")
    by_offset = {}
    for record in records:
        if not isinstance(record, dict) or record.get("kind") != "RecordLayout":
            die("record layout probe returned an invalid record")
        offset = record.get("offset")
        if (type(offset) is not int or offset < 0 or
                type(record.get("token_length")) is not int or
                record["token_length"] <= 0 or
                record.get("tag_kind") not in ("struct", "union") or
                type(record.get("size_bytes")) is not int or
                record["size_bytes"] < 0 or
                type(record.get("alignment_bytes")) is not int or
                record["alignment_bytes"] < 0 or
                not isinstance(record.get("fields"), list)):
            die("record layout probe returned an invalid record")
        by_offset.setdefault(offset, []).append(record)
    return by_offset


def check_profile():
    """The envelope ASSERTS a profile; refuse to assert one this host fails."""
    probe_py = os.path.join(ROOT, "harness", "c_profile_probe.py")
    profile_json = os.path.join(ROOT, "docs", "c-profile.json")
    for p in (probe_py, profile_json):
        if not os.path.exists(p):
            die("%s is missing; the envelope cannot claim %s without it"
                % (os.path.relpath(p, ROOT), PROFILE_ID))
    spec = importlib.util.spec_from_file_location("c_profile_probe", probe_py)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    with open(profile_json) as fh:
        profile = json.load(fh)
    for f in profile["facts"]:
        if f["depended_on"] and mod.probe_fact(None, f["expr"]) != f["required"]:
            die("this host FAILS the profile on %s (%s); it cannot produce a "
                "%s envelope.  %s" % (f["id"], f["expr"], PROFILE_ID, f["why"]))


class Loc:
    """clang's location state.  `file` and `line` are STICKY."""

    def __init__(self, target):
        self.file = None
        self.line = None
        self.target = target

    def absorb(self, slot):
        if not isinstance(slot, dict):
            return None
        expansion = slot.get("expansionLoc") or {}
        spelling = slot.get("spellingLoc") or {}
        inner = expansion or spelling or slot
        # Clang omits `file` from an expansionLoc when a macro is invoked
        # from the main file, while spellingLoc still carries the source file.
        # Keep the expansion line/offset, but recover file identity from the
        # parser's spelling location so macro-generated top-level declarations
        # are not silently dropped by the main-file admission check.
        if not inner.get("file") and spelling.get("file"):
            self.file = spelling["file"]
        if inner.get("file"):
            self.file = inner["file"]
        if inner.get("line"):
            self.line = inner["line"]
        return inner

    def mine(self):
        return self.file is not None and os.path.basename(self.file) == self.target


def span_of(node, loc):
    """Resolve a node's span against the sticky state, and name its macro."""
    rng = node.get("range") or {}
    begin_raw, end_raw = rng.get("begin") or {}, rng.get("end") or {}
    loc.absorb(node.get("loc"))
    b = loc.absorb(begin_raw) or {}
    start_line = loc.line
    e = loc.absorb(end_raw) or {}
    # `col` is OMITTED when clang did not give one -- the same shape the
    # `macro` field below uses, so the schema has ONE spelling for absence.
    # clang knows some locations only to a line (an unnamed parameter in a
    # prototype is the common case) and emitting `null`, or worse a 0, would
    # put a value where the frontend had none.  Measured: this is what gated
    # 199 of 300 gcc.c-torture tests at the ingester (2026-08-24-c-18).
    span = {"line": start_line, "end_line": loc.line}
    if b.get("col") is not None:
        span["col"] = b["col"]
    if e.get("col") is not None:
        span["end_col"] = e["col"]
    # A construct produced by a macro has a spelling location distinct from
    # its expansion location.  Emit the macro only then, so macro-free
    # sources stay byte-identical to a schema without the field.
    sp = (begin_raw.get("spellingLoc") or {})
    ex = (begin_raw.get("expansionLoc") or {})
    if sp and ex and sp.get("line") != ex.get("line"):
        span["macro"] = {"line": sp.get("line"), "col": sp.get("col")}
    return span


def qual(node):
    return ((node.get("type") or {}).get("qualType"))


def kids(node):
    return [c for c in (node.get("inner") or []) if isinstance(c, dict)]


def nonempty(node):
    """clang fills absent ForStmt slots with {}; those are holes, not nodes."""
    return [c if (isinstance(c, dict) and c.get("kind")) else None
            for c in (node.get("inner") or [])]


class Extractor:
    def __init__(self, target, source_text, string_bytes=None, floating_bits=None,
                 record_layouts=None):
        self.loc = Loc(target)
        self.text = source_text
        self.string_bytes = string_bytes
        self.floating_bits = floating_bits
        self.record_layouts = record_layouts
        self.lines = source_text.splitlines()
        self.labels = {}
        self.unsupported = 0

    def collect_labels(self, node):
        if isinstance(node, dict):
            if node.get("kind") == "LabelStmt" and node.get("declId"):
                self.labels[node["declId"]] = node.get("name")
            for c in kids(node):
                self.collect_labels(c)

    def slice_text(self, node):
        rng = node.get("range") or {}
        b, e = (rng.get("begin") or {}), (rng.get("end") or {})
        bo, eo = b.get("offset"), e.get("offset")
        if bo is None or eo is None:
            return node.get("kind", "?")
        raw = self.text[bo:eo + (e.get("tokLen") or 0)]
        raw = " ".join(raw.split())
        return raw[:200]

    def unsupported_leaf(self, node, span):
        self.unsupported += 1
        return {"kind": "Unsupported", "c_kind": node.get("kind", "?"),
                "text": self.slice_text(node), "span": span}

    def node(self, n):
        if n is None:
            return None
        span = span_of(n, self.loc)
        k = n.get("kind")
        # GNU case ranges are a distinct clang CaseStmt shape (`isGNURange`)
        # with two label expressions. The envelope has one `value` slot, so
        # retaining the lower endpoint would silently turn `case lo ... hi`
        # into `case lo`. Refuse the parser node loudly until the AST carries
        # both endpoints.
        if k not in VOCAB:
            return self.unsupported_leaf(n, span)
        fn = getattr(self, "e_" + k, None)
        if fn is None:
            return self.unsupported_leaf(n, span)
        # THE INSTRUMENT'S OWN FIELDS ARE NOT MERGEABLE.  `kind` and `span`
        # are written HERE, by the extractor, about the node; everything else
        # comes from the handler.  `update` let a handler silently overwrite
        # them, which is the field-collision shape the ES lane hit for real
        # (node type written to `kind`, then source properties merged over it,
        # and a `VariableDeclaration`'s own `kind` won).
        #
        # Measured on this extractor at the sweep (2026-08-25-c-25): NO
        # handler returns `kind` or `span`, and none builds a dict with a
        # source-chosen key -- so no collision exists.  The channel is closed
        # anyway, LOUDLY, because "no handler does this today" is a fact about
        # 36 functions and not about the next one.
        payload = fn(n)
        clash = sorted(set(payload) & {"kind", "span"})
        if clash:
            die("internal: handler e_%s returned %s, which are the "
                "EXTRACTOR's fields for this node. A handler that names them "
                "is overwriting the instrument with its subject." % (k, clash))
        out = {"kind": k, "span": span}
        out.update(payload)
        return out

    def seq(self, ns):
        return [self.node(c) for c in ns]

    # ---- declarations -------------------------------------------------
    def e_FunctionDecl(self, n):
        body = next((c for c in kids(n) if c.get("kind") == "CompoundStmt"), None)
        params = [c for c in kids(n) if c.get("kind") == "ParmVarDecl"]
        return {"decl_id": n.get("id"), "name": n.get("name"), "type": qual(n),
                "storage": n.get("storageClass"),
                "variadic": bool(n.get("variadic")),
                "params": self.seq(params),
                "body": self.node(body) if body else None}

    def e_VarDecl(self, n):
        init = kids(n)[-1] if n.get("init") and kids(n) else None
        return {"decl_id": n.get("id"), "name": n.get("name"), "type": qual(n),
                "storage": n.get("storageClass"),
                "va_list": "__va_list_tag" in (n.get("type") or {}).get("desugaredQualType", ""),
                "init": self.node(init) if init else None}

    def e_ParmVarDecl(self, n):
        # `name` is OMITTED when the parameter has none -- C permits it
        # (§6.7.6.3: `int f(int);`) and clang reports no `name`.  Same shape
        # as `col` and `macro`: one spelling for absence, and never a
        # synthetic, which would be a fabricated name one field over from a
        # fabricated column.
        out = {"decl_id": n.get("id"), "type": qual(n)}
        out["va_list"] = "__va_list_tag" in (n.get("type") or {}).get("desugaredQualType", "")
        if n.get("name") is not None:
            out["name"] = n["name"]
        return out

    def e_FieldDecl(self, n):
        # A BIT-FIELD IS NOT ITS DECLARED TYPE.  clang marks the declarator
        # `isBitfield` and puts the width in an inner ConstantExpr; the
        # `qualType` stays `unsigned int`.  Dropping the width -- which this
        # handler did -- hands the model `unsigned int bitfield;`, a DIFFERENT
        # PROGRAM, and the model then answers correctly about the wrong one:
        # 20031211-1.c stored 0xbeef into a one-bit field and read 0xbeef back.
        # Same shape as c-div-2 (docs/backlog/c.md 2026-08-24-c-23), where the
        # dropped key was `array_filler`.
        #
        # An unreadable width DIES rather than degrading to "not a bit-field",
        # because that degradation is exactly the silence this is fixing.
        out = {"name": n.get("name"), "type": qual(n)}
        if n.get("isBitfield"):
            w = next((c for c in kids(n) if c.get("kind") == "ConstantExpr"), None)
            v = None if w is None else w.get("value")
            if v is None or not str(v).isdigit():
                raise SystemExit(
                    "extract.py: FieldDecl %r is a bit-field and its width is not a "
                    "readable constant (%r). The width cannot be dropped: a bit-field "
                    "laid out as its declared type is a different program." % (n.get("name"), v))
            out["bits"] = int(v)
        return out

    def e_RecordDecl(self, n):
        # Record and field attributes change the layout, so they cannot be
        # dropped while retaining an apparently ordinary record. Keep every
        # non-field child as an Unsupported declaration. For a field, retain
        # the field only when its children are the already-modelled bit-field
        # width ConstantExpr; any other child (PackedAttr, AlignedAttr, …)
        # becomes an Unsupported declaration and the layout walker refuses
        # the containing record. This preserves the AST evidence and prevents
        # natural-alignment layout for a packed or aligned record.
        members = []
        for child in kids(n):
            if child.get("kind") != "FieldDecl":
                members.append(self.node(child))
                continue
            allowed = {"ConstantExpr"} if child.get("isBitfield") else set()
            extras = [c for c in kids(child) if c.get("kind") not in allowed]
            if extras:
                members.extend(self.node(c) for c in extras)
            else:
                members.append(self.node(child))
        out = {"decl_id": n.get("id"), "name": n.get("name"), "fields": members}
        if self.record_layouts is not None:
            offset = ((n.get("range") or {}).get("begin") or {}).get("offset")
            if offset is not None:
                matches = self.record_layouts.get(offset, [])
                if matches:
                    out["record_layout"] = matches.pop(0)
        return out

    def e_TypedefDecl(self, n):
        under = next((c for c in kids(n) if c.get("kind") in TYPES), None)
        return {"name": n.get("name"), "type": qual(n),
                "underlying": self.type_node(under) if under else None}

    def e_EnumDecl(self, n):
        return {"name": n.get("name"),
                "constants": self.seq([c for c in kids(n)
                                       if c.get("kind") == "EnumConstantDecl"])}

    def e_EnumConstantDecl(self, n):
        # clang wraps the value in a `ConstantExpr`; it is FLATTENED here,
        # because an enum constant's meaning is the folded integer and every
        # consumer wants the number rather than the tree.  All 11 in-corpus
        # `ConstantExpr` nodes are exactly these.  Where a `ConstantExpr` is
        # NOT flattenable (bit-field widths, rung R2) it is emitted as a node.
        # `value` is OMITTED when clang folded none -- the absence family
        # again (see `col`, and a parameter's `name`).  A fabricated "0"
        # would read exactly like a folded value somebody would then use.
        v = next((c for c in kids(n) if c.get("kind") == "ConstantExpr"), None)
        out = {"decl_id": n.get("id"), "name": n.get("name")}
        if (v or {}).get("value") is not None:
            out["value"] = v["value"]
        return out

    def e_EmptyDecl(self, n):
        return {}

    # ---- the structured type tree (typedefs only) ---------------------
    def type_node(self, t):
        if t is None:
            return None
        k = t.get("kind")
        out = {"kind": k, "type": qual(t)}
        if k not in TYPES:
            return {"kind": "Unsupported", "c_kind": k, "text": qual(t) or "?"}
        sub = [c for c in kids(t) if c.get("kind") in TYPES]
        if k == "BuiltinType":
            out["name"] = qual(t)
        elif k in ("PointerType", "ParenType", "ElaboratedType"):
            out["inner"] = self.type_node(sub[0]) if sub else None
        elif k == "FunctionProtoType":
            out["ret"] = self.type_node(sub[0]) if sub else None
            out["params"] = [self.type_node(c) for c in sub[1:]]
        return out

    # ---- statements ---------------------------------------------------
    def e_CompoundStmt(self, n):
        return {"body": self.seq(kids(n))}

    def e_DeclStmt(self, n):
        decls = self.seq(kids(n))
        # Clang emits a local RecordDecl immediately before the VarDecl that
        # uses it. Retain that parser identity on the variable; consumers can
        # key layout by the declaration ID without parsing qualType strings.
        for i, decl in enumerate(decls):
            if decl.get("kind") == "VarDecl" and i > 0:
                prev = decls[i - 1]
                if prev.get("kind") == "RecordDecl" and prev.get("decl_id"):
                    decl["record_decl_id"] = prev["decl_id"]
        return {"decls": decls}

    def e_IfStmt(self, n):
        c = nonempty(n)
        return {"cond": self.node(c[0] if len(c) > 0 else None),
                "then": self.node(c[1] if len(c) > 1 else None),
                "else": self.node(c[2]) if n.get("hasElse") and len(c) > 2 else None}

    def e_ForStmt(self, n):
        # clang emits five slots: init, condition-variable, cond, inc, body.
        c = nonempty(n) + [None] * 5
        return {"init": self.node(c[0]), "cond": self.node(c[2]),
                "inc": self.node(c[3]), "body": self.node(c[4])}

    def e_WhileStmt(self, n):
        c = nonempty(n)
        return {"cond": self.node(c[-2] if len(c) > 1 else None),
                "body": self.node(c[-1] if c else None)}

    def e_DoStmt(self, n):
        c = nonempty(n)
        return {"body": self.node(c[0] if c else None),
                "cond": self.node(c[1] if len(c) > 1 else None)}

    def e_ReturnStmt(self, n):
        c = kids(n)
        return {"value": self.node(c[0]) if c else None}

    def e_BreakStmt(self, n):
        return {}

    def e_ContinueStmt(self, n):
        return {}

    def e_NullStmt(self, n):
        return {}

    def e_SwitchStmt(self, n):
        c = nonempty(n)
        return {"cond": self.node(c[0] if c else None),
                "body": self.node(c[1] if len(c) > 1 else None)}

    def e_CaseStmt(self, n):
        c = kids(n)
        if n.get("isGNURange"):
            if len(c) < 3:
                raise SystemExit("extract.py: GNU CaseStmt did not retain both endpoints")
            return {"lo": self.node(c[0]), "hi": self.node(c[1]),
                    "body": self.node(c[2]), "gnu_range": True}
        return {"value": self.node(c[0] if c else None),
                "body": self.node(c[1] if len(c) > 1 else None)}

    def e_DefaultStmt(self, n):
        c = kids(n)
        return {"body": self.node(c[0]) if c else None}

    def e_GotoStmt(self, n):
        return {"label": self.labels.get(n.get("targetLabelDeclId"))}

    def e_LabelStmt(self, n):
        c = kids(n)
        return {"label": n.get("name"),
                "body": self.node(c[0]) if c else None}

    # ---- expressions ---------------------------------------------------
    def e_IntegerLiteral(self, n):
        return {"value": n.get("value"), "type": qual(n)}

    def e_CharacterLiteral(self, n):
        return {"value": n.get("value"), "type": qual(n)}

    def e_StringLiteral(self, n):
        out = {"value": n.get("value"), "type": qual(n)}
        if self.string_bytes is not None:
            begin = (n.get("range") or {}).get("begin") or {}
            offset = begin.get("offset")
            # Macro arguments have no direct file offset in the JSON AST.  The
            # expansion location is the parser's source identity for the
            # semantic node, and the probe reports that same location.
            if offset is None:
                offset = (begin.get("expansionLoc") or {}).get("offset")
            if offset is None:
                return out
            if offset not in self.string_bytes:
                die("string byte probe did not observe StringLiteral at offset %r" % offset)
            record = self.string_bytes[offset].pop(0)
            if record.get("kind_name") == "ordinary" and record.get("char_byte_width") == 1:
                out["decoded_bytes"] = record.get("bytes")
        return out

    def e_FloatingLiteral(self, n):
        out = {"value": n.get("value"), "type": qual(n)}
        if self.floating_bits is not None:
            begin = (n.get("range") or {}).get("begin") or {}
            offset = begin.get("offset")
            if offset is None:
                # Macro-expanded literals carry the source-file identity in
                # Clang's expansionLoc; spellingLoc points into a builtin or
                # header buffer and cannot join to this envelope.
                offset = (begin.get("expansionLoc") or {}).get("offset")
            if offset is None:
                return out
            if offset not in self.floating_bits:
                die("floating bits probe did not observe FloatingLiteral at offset %r" % offset)
            record = self.floating_bits[offset].pop(0)
            out["float_bits_hex"] = record["bits_hex"]
            out["float_bit_width"] = record["bit_width"]
        return out

    def e_CXXBoolLiteralExpr(self, n):
        # Clang supplies the parser's semantic boolean value; retain it as a
        # boolean field rather than reparsing the source spelling.
        return {"value": n.get("value"), "type": qual(n)}

    def e_ChooseExpr(self, n):
        cs = kids(n)
        if len(cs) != 3:
            raise SystemExit("extract.py: ChooseExpr did not retain condition and both branches")
        return {"cond": self.node(cs[0]), "then": self.node(cs[1]),
                "else": self.node(cs[2]), "type": qual(n)}

    def e_DeclRefExpr(self, n):
        d = n.get("referencedDecl") or {}
        return {"decl_id": d.get("id"), "name": d.get("name"),
                "decl_kind": d.get("kind"),
                "type": qual(n)}

    def e_MemberExpr(self, n):
        c = kids(n)
        return {"base": self.node(c[0]) if c else None,
                "member": n.get("name"), "arrow": bool(n.get("isArrow")),
                "type": qual(n)}

    def e_ArraySubscriptExpr(self, n):
        c = kids(n)
        return {"base": self.node(c[0] if c else None),
                "index": self.node(c[1] if len(c) > 1 else None),
                "type": qual(n)}

    def e_CallExpr(self, n):
        c = kids(n)
        return {"callee": self.node(c[0] if c else None),
                "args": self.seq(c[1:]), "type": qual(n)}

    def e_BinaryOperator(self, n):
        c = kids(n)
        return {"op": n.get("opcode"),
                "lhs": self.node(c[0] if c else None),
                "rhs": self.node(c[1] if len(c) > 1 else None),
                "type": qual(n)}

    def e_CompoundAssignOperator(self, n):
        c = kids(n)
        return {"op": n.get("opcode"),
                "lhs": self.node(c[0] if c else None),
                "rhs": self.node(c[1] if len(c) > 1 else None),
                "compute_lhs_type": (n.get("computeLHSType") or {}).get("qualType"),
                "compute_result_type": (n.get("computeResultType") or {}).get("qualType"),
                "type": qual(n)}

    def e_UnaryOperator(self, n):
        c = kids(n)
        return {"op": n.get("opcode"), "sub": self.node(c[0] if c else None),
                "postfix": bool(n.get("isPostfix")), "type": qual(n)}

    def e_ConditionalOperator(self, n):
        c = kids(n)
        return {"cond": self.node(c[0] if c else None),
                "then": self.node(c[1] if len(c) > 1 else None),
                "else": self.node(c[2] if len(c) > 2 else None),
                "type": qual(n)}

    def e_ParenExpr(self, n):
        c = kids(n)
        return {"sub": self.node(c[0]) if c else None, "type": qual(n)}

    def e_ImplicitCastExpr(self, n):
        c = kids(n)
        return {"cast": n.get("castKind"),
                "sub": self.node(c[0]) if c else None, "type": qual(n)}

    e_CStyleCastExpr = e_ImplicitCastExpr

    def e_InitListExpr(self, n):
        # Preserve both clang fields, including the leading filler and every
        # positional ImplicitValueInitExpr. Missing means the field was absent,
        # not an empty array. Old envelopes lack this required evidence.
        filler = n.get("array_filler")
        field = (n.get("field") or {}).get("name")
        return {"inits": self.seq(kids(n)),
                "array_filler": None if filler is None else self.seq(filler),
                "field": field,
                "type": qual(n)}

    def e_ImplicitValueInitExpr(self, n):
        return {"type": qual(n)}

    def e_VAArgExpr(self, n):
        c = kids(n)
        if len(c) != 1:
            raise SystemExit("extract.py: VAArgExpr did not retain its cursor operand")
        return {"ap": self.node(c[0]), "type": qual(n)}

    def e_CompoundLiteralExpr(self, n):
        c = kids(n)
        return {"init": self.node(c[0]) if c else None, "type": qual(n)}

    def e_UnaryExprOrTypeTraitExpr(self, n):
        c = kids(n)
        out = {"trait": n.get("name"), "type": qual(n)}
        if n.get("argType"):
            out["arg_type"] = n["argType"].get("qualType")
        else:
            out["sub"] = self.node(c[0]) if c else None
        return out

    def e_ConstantExpr(self, n):
        c = kids(n)
        v = n.get("value")
        def folded(node):
            if node.get("value") is not None:
                return node.get("value")
            for child in kids(node):
                got = folded(child)
                if got is not None:
                    return got
            return None
        if v is None and c:
            v = folded(c[0])
        return {"value": None if v is None else str(v),
                "sub": self.node(c[0]) if c else None, "type": qual(n)}


def externals(tu, target, loc_cls):
    """Declared-but-not-defined names the TU references, with prototypes."""
    defined, decls = set(), {}
    loc = loc_cls(target)
    stack = [tu]
    while stack:
        n = stack.pop()
        if not isinstance(n, dict):
            continue
        loc.absorb(n.get("loc"))
        loc.absorb((n.get("range") or {}).get("begin"))
        if n.get("kind") == "FunctionDecl" and n.get("name"):
            if any(c.get("kind") == "CompoundStmt" for c in kids(n)):
                if loc.mine():
                    defined.add(n["name"])
            else:
                decls.setdefault(n["name"], qual(n))
        stack.extend(reversed(kids(n)))
    used = set()

    # The reference must itself be IN the censused file.  Without this the
    # walk collects names the system headers reference from their own macro
    # bodies -- measured: `__builtin_bswap32`, `__builtin_bswap64`, `__swbuf`,
    # none of which appear anywhere in the corpus's text.  The census applies
    # the same filter, and the two agreeing is the point.
    rloc = loc_cls(target)

    def refs(n):
        if isinstance(n, dict):
            rloc.absorb(n.get("loc"))
            rloc.absorb((n.get("range") or {}).get("begin"))
            if n.get("kind") == "DeclRefExpr" and rloc.mine():
                d = n.get("referencedDecl") or {}
                if d.get("kind") == "FunctionDecl" and d.get("name"):
                    used.add(d["name"])
            for c in kids(n):
                refs(c)
    refs(tu)
    return [{"name": nm, "type": decls.get(nm)}
            for nm in sorted(used - defined)]


def extract(path, source_name=None, standard="c23"):
    global PROFILE_FLAGS, AST_FLAGS
    if standard not in ("c17", "c23"):
        die("unsupported C standard %s" % standard)
    PROFILE_FLAGS = ["-std=" + standard, "-D_FORTIFY_SOURCE=0"]
    AST_FLAGS = PROFILE_FLAGS + ["-fsyntax-only", "-Xclang", "-ast-dump=json"]
    check_profile()
    src = open(path, "rb").read()
    tu = canonicalize_ids(clang_json(path))
    target = os.path.basename(path)
    string_bytes = string_byte_records(path)
    floating_bits = floating_bit_records(path)
    record_layouts = record_layout_records(path)
    ex = Extractor(target, src.decode(), string_bytes, floating_bits, record_layouts)
    ex.collect_labels(tu)

    # Top-level decls attributed to the censused file, in document order.
    loc = Loc(target)
    top = []
    for d in kids(tu):
        loc.absorb(d.get("loc"))
        loc.absorb((d.get("range") or {}).get("begin"))
        if loc.mine():
            ex.loc.file, ex.loc.line = loc.file, loc.line
            top.append(ex.node(d))

    # Clang emits separate declaration IDs for a prototype and its later
    # definition.  In C those declarations denote one function; retaining the
    # prototype ID at a call makes the evaluator refuse a real defined call as
    # external libc.  Use the parser's own FunctionDecl name/body fields to
    # canonicalize redeclarations to the body-bearing declaration ID.  This is
    # identity normalization over the approved AST, never source reparsing.
    function_defs = {
        n.get("name"): n.get("decl_id")
        for n in top
        if n.get("kind") == "FunctionDecl" and n.get("body") is not None
        and n.get("name") and n.get("decl_id")
    }
    def unify(value):
        if isinstance(value, dict):
            if value.get("kind") == "FunctionDecl" and value.get("name") in function_defs:
                value["decl_id"] = function_defs[value["name"]]
            elif value.get("kind") == "DeclRefExpr" and value.get("decl_kind") == "FunctionDecl":
                if value.get("name") in function_defs:
                    value["decl_id"] = function_defs[value["name"]]
            for child in value.values():
                unify(child)
        elif isinstance(value, list):
            for child in value:
                unify(child)
    unify(top)

    # The corpus lives in ANOTHER repository (tools/ctwin/ in sunfish), so a
    # path relative to this root would be a fiction.  `--source-name` records
    # the corpus's own path in its own repo; without it we fall back to a
    # repo-relative path, then to the bare basename.
    if source_name:
        rel = source_name
    else:
        try:
            rel = os.path.relpath(os.path.abspath(path), ROOT)
        except ValueError:
            rel = os.path.basename(path)
        if rel.startswith(".."):
            rel = os.path.basename(path)
    return {
        "schema_version": SCHEMA_VERSION,
        "language": "c",
        "frontend": {"name": "clang-ast-json", "version": frontend_version()},
        "profile_id": PROFILE_ID + ("-c17" if standard == "c17" else ""),
        "profile_flags": PROFILE_FLAGS,
        "source_file": rel,
        "source_sha256": hashlib.sha256(src).hexdigest(),
        "translation_unit": {"kind": "TranslationUnit", "decls": top},
        "externals": externals(tu, target, Loc),
        "lean_blocks": [],
    }, ex.unsupported


def selftest():
    """The field-collision guard, EXECUTED — the sweep's own check.

    A negative result ("no handler collides") is a claim about the 36
    handlers that exist. This lowers a node through a handler that DOES
    collide and requires the extractor to die, so the claim stays true for
    the 37th.
    """
    ok = True

    def check(name, got, want):
        nonlocal ok
        good = got == want
        ok = ok and good
        print("  %-54s %s" % (name, "ok" if good else "FAIL got=%r" % (got,)))

    ex = Extractor("selftest.c", "")
    node = {"kind": "ParenExpr", "range": {}, "type": {"qualType": "int"}}

    # 1. the ordinary path still assembles kind/span from the INSTRUMENT
    ex.e_ParenExpr = lambda n: {"sub": None, "type": "int"}
    out = ex.node(node)
    check("instrument writes `kind` for a normal handler", out.get("kind"), "ParenExpr")
    check("instrument writes `span` for a normal handler", "span" in out, True)

    # 2. a handler that names the instrument's fields DIES rather than winning
    for bad in ({"kind": "NotThis", "sub": None}, {"span": {"line": 999}, "sub": None}):
        ex.e_ParenExpr = lambda n, b=bad: b
        label = "kind" if "kind" in bad else "span"
        try:
            ex.node(node)
            check("a handler returning %r is refused" % label, "accepted", "refused")
        except SystemExit:
            check("a handler returning %r is refused" % label, "refused", "refused")

    print("extract --selftest:", "ok" if ok else "FAILED")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("source", nargs="?")
    ap.add_argument("-o", "--output")
    ap.add_argument("--source-name", metavar="PATH",
                    help="the path to record as source_file (the corpus lives "
                         "in another repository, so its own path is not "
                         "relative to this one)")
    ap.add_argument("--std", choices=("c17", "c23"), default="c23",
                    help="C language edition for the pinned frontend")
    ap.add_argument("--selftest", action="store_true",
                    help="run the instrument's own checks; no clang, no source")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if not args.source:
        die("no source given (and --selftest was not requested)")
    if not os.path.exists(args.source):
        die("no such file: %s" % args.source)
    env, unsup = extract(args.source, args.source_name, args.std)
    text = json.dumps(env, indent=2) + "\n"
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text)
        print("wrote %s (%d top-level decls, %d externals, %d Unsupported)"
              % (args.output, len(env["translation_unit"]["decls"]),
                 len(env["externals"]), unsup))
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
