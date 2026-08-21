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
import re
import subprocess
import sys

SCHEMA_VERSION = "c-0.1"
PROFILE_ID = "c-profile-0.1"
PROFILE_FLAGS = ["-std=c23", "-D_FORTIFY_SOURCE=0"]
AST_FLAGS = PROFILE_FLAGS + ["-fsyntax-only", "-Xclang", "-ast-dump=json"]

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

DECLS = {"FunctionDecl", "VarDecl", "ParmVarDecl", "FieldDecl", "RecordDecl",
         "TypedefDecl", "EnumDecl", "EnumConstantDecl"}
STMTS = {"CompoundStmt", "DeclStmt", "IfStmt", "ForStmt", "WhileStmt", "DoStmt",
         "ReturnStmt", "BreakStmt", "ContinueStmt", "GotoStmt", "LabelStmt"}
EXPRS = {"IntegerLiteral", "CharacterLiteral", "StringLiteral", "FloatingLiteral",
         "DeclRefExpr", "MemberExpr", "ArraySubscriptExpr", "CallExpr",
         "BinaryOperator", "CompoundAssignOperator", "UnaryOperator",
         "ConditionalOperator", "ParenExpr", "ImplicitCastExpr", "CStyleCastExpr",
         "InitListExpr", "CompoundLiteralExpr", "UnaryExprOrTypeTraitExpr",
         "ConstantExpr"}
TYPES = {"BuiltinType", "PointerType", "RecordType", "TypedefType",
         "ElaboratedType", "ParenType", "FunctionProtoType"}
VOCAB = DECLS | STMTS | EXPRS | TYPES


def die(msg):
    sys.exit("extract.py: " + msg)


def clang_json(path):
    out = subprocess.run(["clang"] + AST_FLAGS + [path],
                         capture_output=True, text=True)
    if out.returncode != 0:
        die("clang rejected %s (exit %d).  A partial AST is a DIFFERENT "
            "program, not a smaller one:\n%s" % (path, out.returncode,
                                                 out.stderr[:2000]))
    if not out.stdout:
        die("clang produced no AST for %s\n%s" % (path, out.stderr[:2000]))
    return json.loads(out.stdout)


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


def frontend_family():
    out = subprocess.run(["clang", "--version"], capture_output=True, text=True)
    m = re.search(r"(Apple clang|clang) version (\d+)", out.stdout or "")
    if not m:
        die("cannot determine the clang version family")
    return ("apple-clang-%s" if m.group(1) == "Apple clang" else "clang-%s") % m.group(2)


class Loc:
    """clang's location state.  `file` and `line` are STICKY."""

    def __init__(self, target):
        self.file = None
        self.line = None
        self.target = target

    def absorb(self, slot):
        if not isinstance(slot, dict):
            return None
        inner = slot.get("expansionLoc") or slot.get("spellingLoc") or slot
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
    span = {"line": start_line, "col": b.get("col"),
            "end_line": loc.line, "end_col": e.get("col")}
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
    def __init__(self, target, source_text):
        self.loc = Loc(target)
        self.text = source_text
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
        if k not in VOCAB:
            return self.unsupported_leaf(n, span)
        fn = getattr(self, "e_" + k, None)
        if fn is None:
            return self.unsupported_leaf(n, span)
        out = {"kind": k, "span": span}
        out.update(fn(n))
        return out

    def seq(self, ns):
        return [self.node(c) for c in ns]

    # ---- declarations -------------------------------------------------
    def e_FunctionDecl(self, n):
        body = next((c for c in kids(n) if c.get("kind") == "CompoundStmt"), None)
        params = [c for c in kids(n) if c.get("kind") == "ParmVarDecl"]
        return {"name": n.get("name"), "type": qual(n),
                "storage": n.get("storageClass"),
                "params": self.seq(params),
                "body": self.node(body) if body else None}

    def e_VarDecl(self, n):
        init = kids(n)[-1] if n.get("init") and kids(n) else None
        return {"name": n.get("name"), "type": qual(n),
                "storage": n.get("storageClass"),
                "init": self.node(init) if init else None}

    def e_ParmVarDecl(self, n):
        return {"name": n.get("name"), "type": qual(n)}

    def e_FieldDecl(self, n):
        return {"name": n.get("name"), "type": qual(n)}

    def e_RecordDecl(self, n):
        return {"name": n.get("name"),
                "fields": self.seq([c for c in kids(n)
                                    if c.get("kind") == "FieldDecl"])}

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
        v = next((c for c in kids(n) if c.get("kind") == "ConstantExpr"), None)
        return {"name": n.get("name"),
                "value": (v or {}).get("value")}

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
        return {"decls": self.seq(kids(n))}

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
        return {"value": n.get("value"), "type": qual(n)}

    def e_FloatingLiteral(self, n):
        return {"value": n.get("value"), "type": qual(n)}

    def e_DeclRefExpr(self, n):
        d = n.get("referencedDecl") or {}
        return {"name": d.get("name"), "decl_kind": d.get("kind"),
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

    e_CompoundAssignOperator = e_BinaryOperator

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
        return {"inits": self.seq(kids(n)), "type": qual(n)}

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
        return {"value": n.get("value"),
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


def extract(path, source_name=None):
    check_profile()
    src = open(path, "rb").read()
    tu = clang_json(path)
    target = os.path.basename(path)
    ex = Extractor(target, src.decode())
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
        "frontend": {"name": "clang-ast-json", "version": frontend_family()},
        "profile_id": PROFILE_ID,
        "profile_flags": PROFILE_FLAGS,
        "source_file": rel,
        "source_sha256": hashlib.sha256(src).hexdigest(),
        "translation_unit": {"kind": "TranslationUnit", "decls": top},
        "externals": externals(tu, target, Loc),
        "lean_blocks": [],
    }, ex.unsupported


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("source")
    ap.add_argument("-o", "--output")
    ap.add_argument("--source-name", metavar="PATH",
                    help="the path to record as source_file (the corpus lives "
                         "in another repository, so its own path is not "
                         "relative to this one)")
    args = ap.parse_args()
    if not os.path.exists(args.source):
        die("no such file: %s" % args.source)
    env, unsup = extract(args.source, args.source_name)
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
