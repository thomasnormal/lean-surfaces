#!/usr/bin/env python3
"""c_construct_census.py — the C tier's construct census, from the sources.

Measures which C the corpus actually USES: node kinds, operators, the
conversion lattice, control flow, the libc surface, the object kinds, and
the two facts the C tier's shape turns on (address-of on automatics, and
the sequencing candidates).  Every number `docs/c-tier-charter.md` quotes
comes from here; nothing there is quoted from memory.

    python3 harness/c_construct_census.py <file.c> [-o out.json]
    python3 harness/c_construct_census.py <file.c> --compare docs/….json

`--compare` prints the delta against a previous run's JSON, which is what
makes a stale census DETECTABLE rather than merely possible: the corpus
lives in another repository and moves on its own schedule.

THE PINNED PROFILE IS AN INPUT, NOT A STAMP.  Under this host's default
headers `_FORTIFY_SOURCE` rewrites `memcpy`/`strcpy`/`sprintf`/`snprintf`
into `__builtin___*_chk` and injects `__builtin_object_size` nodes that
are in nobody's source — so the same file censuses differently.  The
flags below are therefore part of the measurement and are recorded in
every output.

Counting rule: clang's `loc.file` is STICKY (a node omits the file when it
repeats its predecessor's), so the walk carries the last-seen file forward
and counts only nodes attributed to the censused source.  Without that
filter the census measures libc's headers.  A run that attributes ZERO
nodes to the source EXITS NON-ZERO — an empty census is an instrument
fault, never a finding.

Python >= 3.9, stdlib only.  Deterministic: every mapping is emitted in
sorted order, so a double run is byte-identical.
"""

import argparse
import collections
import hashlib
import json
import os
import re
import subprocess
import sys

# The pinned profile.  See the module docstring: these flags change the AST.
CLANG_STD = "-std=c23"
CLANG_PROFILE = [CLANG_STD, "-D_FORTIFY_SOURCE=0"]
AST_FLAGS = CLANG_PROFILE + ["-fsyntax-only", "-Xclang", "-ast-dump=json"]

# C23 §6.8: a full expression is one that is not part of another expression.
# The sequencing census (charter §2, "unspecified behavior") runs over these.
FULL_EXPR_PARENTS = {"CompoundStmt", "IfStmt", "WhileStmt", "DoStmt", "ForStmt",
                     "SwitchStmt", "ReturnStmt", "VarDecl", "CaseStmt"}
EXPR_KINDS = re.compile(r"(Expr|Operator|Literal)$")
# An EFFECT is a store, a `++`/`--`, or a call.  Allocation and IO reach the
# model only through calls, so `CallExpr` covers them.
EFFECT_CALL_KINDS = {"CallExpr", "CompoundAssignOperator"}


def run(cmd):
    out = subprocess.run(cmd, capture_output=True, text=True)
    return out


def clang_version():
    out = run(["clang", "--version"])
    first = (out.stdout or "").splitlines()[:1]
    text = first[0] if first else ""
    # The FAMILY, never the point release: stamping `17.0.0 (clang-1700.6.4.2)`
    # re-keys every artifact for a byte-identical payload.  That churn is
    # recorded twice in docs/backlog.md; this is the correction applied up front.
    m = re.search(r"(Apple clang|clang) version (\d+)", text)
    return ("apple-clang-%s" % m.group(2)) if m and m.group(1) == "Apple clang" \
        else ("clang-%s" % m.group(2)) if m else "unknown"


def effects(node):
    """The number of effect SITES inside one expression."""
    n = 0
    kind = node.get("kind")
    if kind in EFFECT_CALL_KINDS:
        n += 1
    elif kind == "BinaryOperator" and node.get("opcode") == "=":
        n += 1
    elif kind == "UnaryOperator" and node.get("opcode") in ("++", "--"):
        n += 1
    for child in node.get("inner") or []:
        if isinstance(child, dict):
            n += effects(child)
    return n


def _file_of(node):
    """The file clang attributes to a node, across its three spellings."""
    for slot in (node.get("loc") or {}, (node.get("range") or {}).get("begin") or {},
                 (node.get("range") or {}).get("end") or {}):
        for key in ("file",):
            if slot.get(key):
                return slot[key]
        for nested in ("expansionLoc", "spellingLoc"):
            if (slot.get(nested) or {}).get("file"):
                return slot[nested]["file"]
    return None


def _strip(node):
    """Peel the wrappers clang inserts around an operand."""
    while isinstance(node, dict) and node.get("kind") in ("ParenExpr", "ImplicitCastExpr"):
        node = (node.get("inner") or [{}])[0]
    return node if isinstance(node, dict) else {}


def walk(node, st, parent=None):
    """Walk in document order, carrying clang's sticky `loc.file` forward."""
    seen = _file_of(node)
    if seen:
        st["file"] = seen
    kind = node.get("kind")
    if kind and st["file"] and os.path.basename(st["file"]) == st["target"]:
        st["hits"].append(node)
        pk = (parent or {}).get("kind")
        if kind == "MemberExpr" and _strip((node.get("inner") or [{}])[0]).get("kind") == "CallExpr":
            # C23 §6.2.4 temporary lifetime: a member read off a call RESULT.
            st["member_on_call"] += 1
        if pk in FULL_EXPR_PARENTS and EXPR_KINDS.search(kind):
            st["full_exprs"] += 1
            if effects(node) >= 2:
                st["multi_effect"].append(node)
        if kind == "VarDecl" and pk == "TranslationUnitDecl":
            st["file_scope"] += 1
            if node.get("inner"):
                st["file_scope_init"] += 1
        if kind == "UnaryOperator" and node.get("opcode") == "&":
            tgt = _strip((node.get("inner") or [{}])[0])
            decl = tgt.get("referencedDecl") or {}
            if tgt.get("kind") == "DeclRefExpr" \
                    and decl.get("kind") in ("VarDecl", "ParmVarDecl") \
                    and decl.get("storageClass") != "static":
                # The address of an AUTOMATIC object is observable, which is
                # why a C local cannot be an environment binding (charter §2).
                st["addr_automatic"] += 1
            elif tgt.get("kind") in ("MemberExpr", "ArraySubscriptExpr"):
                st["addr_subobject"] += 1
        qual = (node.get("type") or {}).get("qualType")
        if qual:
            st["types"][qual] += 1
    for slot in ("inner", "args"):
        for child in node.get(slot) or []:
            if isinstance(child, dict):
                walk(child, st, node)


def census(path):
    ast = run(["clang"] + AST_FLAGS + [path])
    # A clang DIAGNOSTIC still yields a partial AST on stdout.  Censusing it
    # would report a plausible table for a program that does not compile —
    # a silent wrong answer, which this project does not ship.  Refuse.
    if ast.returncode != 0:
        sys.exit("c_construct_census: clang rejected %s (exit %d); the census "
                 "of a program that does not compile would be a wrong answer, "
                 "not a smaller one:\n%s" % (path, ast.returncode, ast.stderr[:2000]))
    if not ast.stdout:
        sys.exit("c_construct_census: clang produced no AST for %s\n%s"
                 % (path, ast.stderr[:2000]))
    st = {"file": None, "target": os.path.basename(path), "hits": [],
          "member_on_call": 0, "full_exprs": 0, "multi_effect": [],
          "file_scope": 0, "file_scope_init": 0, "addr_automatic": 0,
          "addr_subobject": 0, "types": collections.Counter()}
    walk(json.loads(ast.stdout), st)
    if not st["hits"]:
        sys.exit("c_construct_census: ZERO nodes attributed to %s — the "
                 "loc.file filter is wrong, not the corpus" % path)

    hits = st["hits"]
    kinds = collections.Counter(n["kind"] for n in hits)
    of = lambda k: [n for n in hits if n["kind"] == k]
    opcodes = lambda k: collections.Counter(n.get("opcode") for n in of(k))
    castkinds = lambda k: collections.Counter(n.get("castKind") for n in of(k))

    callees, indirect = collections.Counter(), 0
    for call in of("CallExpr"):
        head = _strip((call.get("inner") or [{}])[0])
        decl = head.get("referencedDecl") or {}
        if head.get("kind") == "DeclRefExpr" and decl.get("kind") == "FunctionDecl":
            callees[decl.get("name")] += 1
        else:
            indirect += 1

    bodies = [n for n in of("FunctionDecl")
              if any((i or {}).get("kind") == "CompoundStmt" for i in (n.get("inner") or []))]
    external = sorted(n for n in callees if n not in {b.get("name") for b in bodies})

    src = open(path, "rb").read()
    text = src.decode()
    lines = text.splitlines()
    pp = run(["clang"] + CLANG_PROFILE + ["-E", path])

    ops = dict(sorted(opcodes("BinaryOperator").items()))
    cops = dict(sorted(opcodes("CompoundAssignOperator").items()))
    uops = dict(sorted(opcodes("UnaryOperator").items()))
    overflowing = sum(ops.get(o, 0) for o in ("+", "-", "*")) \
        + sum(uops.get(o, 0) for o in ("-", "++", "--")) \
        + sum(cops.get(o, 0) for o in ("+=", "-=", "*="))

    return {
        "instrument": "harness/c_construct_census.py",
        "profile": {"frontend": clang_version(), "flags": CLANG_PROFILE},
        "source": os.path.basename(path),
        "sha256": hashlib.sha256(src).hexdigest(),
        "lines_total": len(lines),
        "lines_nonblank": sum(1 for l in lines if l.strip()),
        "preprocessed_lines": len(pp.stdout.splitlines()),
        "includes": re.findall(r"^\s*#\s*include\s*[<\"]([^>\"]+)", text, re.M),
        "functions_with_bodies": len(bodies),
        "functions_static": sum(1 for b in bodies if b.get("storageClass") == "static"),
        "file_scope_objects": st["file_scope"],
        "file_scope_objects_initialized": st["file_scope_init"],
        "node_kinds_distinct": len(kinds),
        "node_kinds": dict(sorted(kinds.items())),
        "record_decls": kinds.get("RecordDecl", 0),
        "typedefs": kinds.get("TypedefDecl", 0),
        "enum_decls": kinds.get("EnumDecl", 0),
        "enum_constants": kinds.get("EnumConstantDecl", 0),
        "field_decls": kinds.get("FieldDecl", 0),
        "binary_ops": ops,
        "binary_op_sites": sum(ops.values()),
        "compound_assign_ops": cops,
        "compound_assign_sites": sum(cops.values()),
        "unary_ops": uops,
        "unary_op_sites": sum(uops.values()),
        "overflow_capable_sites": overflowing,
        "implicit_casts": dict(sorted(castkinds("ImplicitCastExpr").items())),
        "implicit_cast_sites": kinds.get("ImplicitCastExpr", 0),
        "cstyle_casts": dict(sorted(castkinds("CStyleCastExpr").items())),
        "cstyle_cast_sites": kinds.get("CStyleCastExpr", 0),
        "call_sites": kinds.get("CallExpr", 0),
        "callees_distinct": len(callees),
        "indirect_calls": indirect,
        "callee_counts": dict(sorted(callees.items())),
        "external_names": external,
        "external_call_sites": sum(callees[n] for n in external),
        "control": {k: kinds.get(k, 0) for k in sorted((
            "IfStmt", "ForStmt", "DoStmt", "WhileStmt", "SwitchStmt", "GotoStmt",
            "LabelStmt", "BreakStmt", "ContinueStmt", "ReturnStmt",
            "ConditionalOperator", "CompoundStmt"))},
        "array_subscripts": kinds.get("ArraySubscriptExpr", 0),
        "member_exprs": kinds.get("MemberExpr", 0),
        "sizeof_sites": kinds.get("UnaryExprOrTypeTraitExpr", 0),
        "compound_literals": kinds.get("CompoundLiteralExpr", 0),
        "string_literals": kinds.get("StringLiteral", 0),
        "float_literals": kinds.get("FloatingLiteral", 0),
        "function_like_macros": len(re.findall(r"^\s*#\s*define\s+\w+\(", text, re.M)),
        "object_like_macros": len(re.findall(r"^\s*#\s*define\s+\w+\s+", text, re.M)),
        "member_on_call_result": st["member_on_call"],
        # `&x` on an automatic object, and `&x.f` / `&x[i]` on a subobject.
        # Both are zero in Python by construction; both are why the C tier's
        # locals live in MEMORY and not in an environment (charter §2).
        "addr_of_automatic": st["addr_automatic"],
        "addr_of_subobject": st["addr_subobject"],
        "full_expr_convention": "C23 6.8 — includes declarator initializers",
        "full_exprs": st["full_exprs"],
        "full_exprs_multi_effect": len(st["multi_effect"]),
        # `x = f(…)`: the store is sequenced AFTER the right operand's value
        # computation, so there is one effect POSITION and the census admits it
        # by inspection.  The remainder is what a may-alias check must cover.
        "multi_effect_single_position": sum(
            1 for n in st["multi_effect"]
            if n.get("kind") == "BinaryOperator" and n.get("opcode") == "="
            and effects((n.get("inner") or [{}])[0]) == 0),
        "multi_effect_shapes": dict(sorted(collections.Counter(
            "%s/%d" % (n["kind"], effects(n)) for n in st["multi_effect"]).items())),
        "scalar_types": {t: n for t, n in sorted(st["types"].items())
                         if not set("*[(").intersection(t)},
    }


def compare(new, old):
    """Print the delta between two census runs.  Kinds first: a NEW node kind
    is a tier decision, a bigger count is only a bigger corpus."""
    print("source   %s" % new["source"])
    print("sha256   %s -> %s" % (old["sha256"][:16], new["sha256"][:16]))
    if old["sha256"] == new["sha256"]:
        print("UNCHANGED — same bytes, nothing to compare")
        return 0
    added = sorted(set(new["node_kinds"]) - set(old["node_kinds"]))
    gone = sorted(set(old["node_kinds"]) - set(new["node_kinds"]))
    print("node kinds  %d -> %d   added: %s   dropped: %s"
          % (len(old["node_kinds"]), len(new["node_kinds"]),
             ", ".join(added) or "none", ", ".join(gone) or "none"))
    nx, ox = set(new["external_names"]), set(old["external_names"])
    print("libc names  %d -> %d   added: %s   dropped: %s"
          % (len(ox), len(nx), ", ".join(sorted(nx - ox)) or "none",
             ", ".join(sorted(ox - nx)) or "none"))
    for key in sorted(new):
        a, b = old.get(key), new[key]
        if isinstance(b, int) and isinstance(a, int) and a != b:
            print("  %-34s %6d -> %6d  (%+d)" % (key, a, b, b - a))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("source", help="the C translation unit to census")
    ap.add_argument("-o", "--output", help="write the census JSON here")
    ap.add_argument("--compare", metavar="JSON",
                    help="print the delta against a previous run and exit")
    args = ap.parse_args()
    if not os.path.exists(args.source):
        sys.exit("c_construct_census: no such file: %s" % args.source)
    data = census(args.source)
    if args.compare:
        with open(args.compare) as fh:
            return compare(data, json.load(fh))
    text = json.dumps(data, indent=2, sort_keys=True) + "\n"
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text)
        print("wrote %s (%s, %d node kinds, sha %s)"
              % (args.output, data["source"], data["node_kinds_distinct"],
                 data["sha256"][:16]))
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
