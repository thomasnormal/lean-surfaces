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

STORAGE DURATION IS RESOLVED BY `id`, NOT BY THE REFERENCE.  Measured on
this host: clang's `referencedDecl` stub carries `id`, `kind`, `name` and
`type` and **never `storageClass`** — so a guard written as
`decl.get("storageClass") != "static"` cannot see the fact it tests and
admits every object designator.  That guard is why `addr_of_automatic`
read 86 when the automatic sites are 31; the other 55 are `&` of a
file-scope object (M2 inch 2's census).  The fix is a PRE-PASS that maps
every `VarDecl`/`ParmVarDecl` `id` to its storage duration, so `&x` is
classified by resolving the id rather than by reading a field that is not
there.  `--selftest` asserts the stub still lacks the field, so the day
clang starts emitting it the instrument says so instead of drifting.

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


def _line_seen(node):
    """The line clang spells on a node, across its three slots.  STICKY: a
    node that repeats its predecessor's line omits the field entirely."""
    for slot in ((node.get("range") or {}).get("begin") or {}, node.get("loc") or {}):
        if slot.get("line"):
            return slot["line"]
        for nested in ("expansionLoc", "spellingLoc"):
            if (slot.get(nested) or {}).get("line"):
                return slot[nested]["line"]
    return None


def _strip(node):
    """Peel the wrappers clang inserts around an operand."""
    while isinstance(node, dict) and node.get("kind") in ("ParenExpr", "ImplicitCastExpr"):
        node = (node.get("inner") or [{}])[0]
    return node if isinstance(node, dict) else {}


def durations(node, out, par=None):
    """Pre-pass: map every object declaration's `id` to its STORAGE DURATION.

    C23 §6.2.4: an object declared at file scope, or with `static`/`extern`,
    has static storage duration; every other declared object is automatic.
    The map is keyed by clang's `id` because the reference site cannot answer
    the question — see the module docstring.  Runs over the WHOLE AST, not
    just the censused file, so a reference into a header still resolves.

    The value is `(duration, scope)`: SCOPE is where it was declared and
    DURATION is how long it lives, and they are different questions — a
    block-scope `static` has block scope and static duration, which is
    exactly the case the memory model's frame discipline must not assume
    away.  Measured on the corpus: zero of them.
    """
    if isinstance(node, list):
        for child in node:
            durations(child, out, par)
        return
    if not isinstance(node, dict):
        return
    kind = node.get("kind")
    if kind in ("VarDecl", "ParmVarDecl") and node.get("id"):
        at_file_scope = kind == "VarDecl" and par == "TranslationUnitDecl"
        static = at_file_scope or (
            kind == "VarDecl" and node.get("storageClass") in ("static", "extern"))
        out[node["id"]] = ("static" if static else "automatic",
                           "file" if at_file_scope else "block")
    for child in node.get("inner") or []:
        durations(child, out, kind or par)


def _dur(st, node_id):
    """The storage DURATION recorded for a declaration id, or None."""
    return (st["durations"].get(node_id) or (None, None))[0]


def _root_designator(node):
    """Walk a subobject designator down to the object it names."""
    for _ in range(64):                       # depth-bounded: no cycles in an AST
        node = _strip(node)
        kind = node.get("kind")
        if kind == "MemberExpr":
            node = (node.get("inner") or [{}])[0]
        elif kind == "ArraySubscriptExpr":
            node = (node.get("inner") or [{}])[0]
        else:
            return node
    return {}


def _callee_name(call):
    """The name a call's callee resolves to, or `<indirect>`."""
    head = _strip((call.get("inner") or [{}])[0])
    return ((head.get("referencedDecl") or {}).get("name")
            or ("<indirect>" if head else "?"))


def _line_of(node):
    """The EXPANSION line, as stamped on the node by `walk`.

    clang's `line` is STICKY exactly like `loc.file` — a node omits it when
    it repeats its predecessor's — so reading it off one node in isolation
    yields 0 for most of the AST.  `walk` carries the last-seen line forward
    and stamps it; this only reads the stamp.
    """
    return node.get("_census_line", 0)


def _is_ptr(node):
    """Does this node have a POINTER type, as clang spells it?"""
    q = (node.get("type") or {}).get("qualType") or ""
    return q.endswith("*") or "*" in q.split("(")[0]


def walk(node, st, parent=None):
    """Walk in document order, carrying clang's sticky `loc.file` forward."""
    seen = _file_of(node)
    if seen:
        st["file"] = seen
    line = _line_seen(node)
    if line:
        st["line"] = line
    node["_census_line"] = st["line"]
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
            # Storage duration comes from the DECLARATION, resolved by id: the
            # reference stub carries no `storageClass` (module docstring).
            dur = _dur(st, decl.get("id"))
            if tgt.get("kind") == "DeclRefExpr" \
                    and decl.get("kind") in ("VarDecl", "ParmVarDecl"):
                # The address of an AUTOMATIC object is observable, which is
                # why a C local cannot be an environment binding (charter §2).
                # `&` of a file-scope object is common too and proves nothing
                # about locals, so the two are counted APART.
                st["addr_static" if dur == "static" else "addr_automatic"] += 1
            elif tgt.get("kind") in ("MemberExpr", "ArraySubscriptExpr"):
                st["addr_subobject"] += 1
                root = _root_designator(tgt)
                rdur = _dur(st, (root.get("referencedDecl") or {}).get("id"))
                st["addr_sub_static" if rdur == "static" else "addr_sub_automatic"] += 1
        if kind == "UnaryOperator" and node.get("opcode") == "*":
            # C23 §6.5.3.2: the indirection operator.  `->` is the OTHER
            # spelling and outnumbers it; both are counted (memory §2).
            st["deref_shapes"][_strip((node.get("inner") or [{}])[0]).get("kind")] += 1
        if kind == "MemberExpr":
            st["member_arrow" if node.get("isArrow") else "member_dot"] += 1
        if kind == "ArraySubscriptExpr":
            base = _strip((node.get("inner") or [{}])[0])
            bk = base.get("kind")
            if bk == "DeclRefExpr":
                bdur = _dur(st, (base.get("referencedDecl") or {}).get("id"))
                st["subscript_bases"]["DeclRefExpr/%s" % (bdur or "?")] += 1
            else:
                st["subscript_bases"][bk] += 1
        if kind == "BinaryOperator":
            kids = [_strip(c) for c in (node.get("inner") or [])]
            if _is_ptr(node) or any(_is_ptr(k) for k in kids):
                st["pointer_binops"][node.get("opcode")] += 1
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
    tree = json.loads(ast.stdout)
    durs = {}
    durations(tree, durs)
    st = {"file": None, "target": os.path.basename(path), "hits": [],
          "member_on_call": 0, "full_exprs": 0, "multi_effect": [],
          "file_scope": 0, "file_scope_init": 0, "addr_automatic": 0,
          "addr_static": 0, "addr_subobject": 0, "addr_sub_automatic": 0,
          "addr_sub_static": 0, "member_arrow": 0, "member_dot": 0,
          "deref_shapes": collections.Counter(),
          "subscript_bases": collections.Counter(),
          "pointer_binops": collections.Counter(),
          "line": 0, "durations": durs, "types": collections.Counter()}
    walk(tree, st)
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

    # ---- J.1 interference census -------------------------------------------
    # C23 §6.5.2.2p10: the evaluations of a call's arguments are INDETERMINATELY
    # SEQUENCED with respect to one another — no interleaving, but either order.
    # Thomas's ruling makes the order a PARAMETER and correctness a `∀ order`
    # claim, so the cheap discharge is a census: where two argument expressions
    # could interfere, and how many such sites there are at all.
    # (§6.5p2's UNSEQUENCED conflicting side effects are a different question —
    # those are UB and REFUSE, not a quantifier.  The partition matters.)
    argc = collections.Counter()
    order_domain, two_effects = [], []
    for call in of("CallExpr"):
        args = (call.get("inner") or [])[1:]
        argc[len(args)] += 1
        if len(args) < 2:
            continue
        neff = sum(1 for a in args if effects(a))
        if neff >= 1:
            order_domain.append(call)
        if neff >= 2:
            two_effects.append(call)
    # The same question for operands of the operators C leaves unsequenced —
    # everything but `&&`, `||`, `?:` and `,`, which are sequence points.
    seqpoints = {"&&", "||", ","}
    unseq_both = 0
    for b in of("BinaryOperator") + of("CompoundAssignOperator"):
        if b.get("opcode") in seqpoints:
            continue
        kids = (b.get("inner") or [])
        if len(kids) == 2 and effects(kids[0]) and effects(kids[1]):
            unseq_both += 1

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
        # STORAGE DURATION IS RESOLVED BY id — see the module docstring; the
        # static split is reported because only the AUTOMATIC count bears on
        # the locals-are-objects decision, and it is the smaller number.
        "addr_of_automatic": st["addr_automatic"],
        "addr_of_static": st["addr_static"],
        "addr_of_subobject": st["addr_subobject"],
        "addr_of_subobject_automatic": st["addr_sub_automatic"],
        "addr_of_subobject_static": st["addr_sub_static"],
        "addr_of_sites": (st["addr_automatic"] + st["addr_static"]
                          + st["addr_subobject"]),
        # M2 inch 2's memory census: how POINTERS are made, and how they are
        # used.  `&` is not the corpus's main pointer producer — decay is.
        "ptr_produced": {
            "address_of": st["addr_automatic"] + st["addr_static"] + st["addr_subobject"],
            "array_to_pointer_decay": castkinds("ImplicitCastExpr").get("ArrayToPointerDecay", 0),
            "function_to_pointer_decay": castkinds("ImplicitCastExpr").get("FunctionToPointerDecay", 0),
            "null_to_pointer": (castkinds("ImplicitCastExpr").get("NullToPointer", 0)
                                + castkinds("CStyleCastExpr").get("NullToPointer", 0)),
            "void_bitcast": castkinds("ImplicitCastExpr").get("BitCast", 0),
        },
        "ptr_consumed": {
            "deref_star": opcodes("UnaryOperator").get("*", 0),
            "member_arrow": st["member_arrow"],
            "member_dot": st["member_dot"],
            "subscript": kinds.get("ArraySubscriptExpr", 0),
            "lvalue_to_rvalue": castkinds("ImplicitCastExpr").get("LValueToRValue", 0),
        },
        "deref_operand_shapes": dict(sorted(
            (k or "?", v) for k, v in st["deref_shapes"].items())),
        "subscript_bases": dict(sorted(
            (k or "?", v) for k, v in st["subscript_bases"].items())),
        "pointer_binops": dict(sorted(
            (k or "?", v) for k, v in st["pointer_binops"].items())),
        # Every block-scope object's storage duration.  ZERO static locals is
        # what lets a frame be created and destroyed as a unit (memory §2.2).
        "block_scope_objects": sum(
            1 for n in of("VarDecl")
            if (st["durations"].get(n.get("id")) or (None, None))[1] == "block"),
        # A block-scope `static` has block SCOPE and static DURATION, so it
        # outlives its frame.  ZERO in the corpus, which is what lets a frame
        # be created and destroyed as a unit (memory §2.2).
        "block_scope_static": sum(
            1 for n in of("VarDecl")
            if (st["durations"].get(n.get("id")) or (None, None)) == ("static", "block")),
        # The J.1 register's evidence (docs/c-semantics-design.md §4.5): the
        # `∀ order` obligation's DOMAIN, and the two shapes that would make it
        # expensive.  Both of those measure ZERO on this corpus.
        "call_sites_by_argc": {str(k): v for k, v in sorted(argc.items())},
        "call_arg_order_domain": len(order_domain),
        "call_arg_two_effects": len(two_effects),
        "call_arg_order_sites": sorted(
            "%s:L%d" % (_callee_name(c), _line_of(c)) for c in order_domain),
        "unsequenced_operands_both_effectful": unseq_both,
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
    """Print the delta between two census runs, and RETURN 1 WHEN IT DRIFTED.
    Kinds first: a NEW node kind is a tier decision, a bigger count is only a
    bigger corpus.

    The exit status is the point.  family-architecture.md §5.4 asks for
    `--compare` "because corpora that live in other repositories move on their
    own schedule and staleness must be mechanically detectable rather than
    merely possible" — and a mode that always exits 0 is detectable only by a
    human reading stdout.  It cannot gate, it cannot run under `set -e`, and
    this instrument is the one §5.4 names as having fixed the contract.
    0 = the committed census still describes the corpus, 1 = it does not."""
    print("source   %s" % new["source"])
    print("sha256   %s -> %s" % (old["sha256"][:16], new["sha256"][:16]))
    if new == old:
        print("UNCHANGED — byte-identical census, nothing to compare")
        return 0
    drift = 0
    if old["sha256"] == new["sha256"]:
        # The second staleness hole, and it was hiding behind the first: the
        # old early return keyed on the SOURCE sha, so a census that differed
        # for the same input — a moved frontend, a changed instrument, a
        # hand-edited artifact — reported UNCHANGED and exited 0.
        print("SAME SOURCE BYTES, DIFFERENT CENSUS — the frontend or this "
              "instrument moved, or the committed artifact was edited by hand")
        drift += 1
    added = sorted(set(new["node_kinds"]) - set(old["node_kinds"]))
    gone = sorted(set(old["node_kinds"]) - set(new["node_kinds"]))
    drift += len(added) + len(gone)
    print("node kinds  %d -> %d   added: %s   dropped: %s"
          % (len(old["node_kinds"]), len(new["node_kinds"]),
             ", ".join(added) or "none", ", ".join(gone) or "none"))
    nx, ox = set(new["external_names"]), set(old["external_names"])
    print("libc names  %d -> %d   added: %s   dropped: %s"
          % (len(ox), len(nx), ", ".join(sorted(nx - ox)) or "none",
             ", ".join(sorted(ox - nx)) or "none"))
    drift += len(nx - ox) + len(ox - nx)
    for key in sorted(new):
        a, b = old.get(key), new[key]
        if isinstance(b, int) and isinstance(a, int) and a != b:
            print("  %-34s %6d -> %6d  (%+d)" % (key, a, b, b - a))
            drift += 1
    print("compare: %d difference(s) — the committed census is STALE" % drift)
    return 1


SELFTEST_C = """static int g;
int f(int prm) { int loc; int *a = &g, *b = &loc, *c = &prm; return *a + *b + *c; }
"""


def selftest():
    """Assert the FRONTEND FACT the storage-duration pre-pass exists for.

    The old guard read `storageClass` off the reference stub, where clang
    does not put it, so it classified `&g` on a file-scope object as
    automatic.  This checks BOTH halves: the field is still absent, and the
    id-resolved classification still separates the three cases.  If clang
    ever starts emitting the field, this fails LOUDLY rather than letting
    the census drift back to a number nobody re-derived.
    """
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, "selftest.c")
        with open(src, "w") as fh:
            fh.write(SELFTEST_C)
        ast = run(["clang"] + AST_FLAGS + [src])
        if ast.returncode != 0 or not ast.stdout:
            sys.exit("c_construct_census --selftest: clang failed\n%s" % ast.stderr[:800])
        tree = json.loads(ast.stdout)
        durs = {}
        durations(tree, durs)
        st = {"file": None, "target": "selftest.c", "hits": [], "member_on_call": 0,
              "full_exprs": 0, "multi_effect": [], "file_scope": 0,
              "file_scope_init": 0, "addr_automatic": 0, "addr_static": 0,
              "addr_subobject": 0, "addr_sub_automatic": 0, "addr_sub_static": 0,
              "member_arrow": 0, "member_dot": 0,
              "deref_shapes": collections.Counter(),
              "subscript_bases": collections.Counter(),
              "pointer_binops": collections.Counter(),
              "line": 0, "durations": durs, "types": collections.Counter()}
        walk(tree, st)
        stubs = []

        def find(n):
            if isinstance(n, dict):
                if n.get("kind") == "DeclRefExpr" and n.get("referencedDecl"):
                    stubs.append(n["referencedDecl"])
                for v in n.values():
                    find(v)
            elif isinstance(n, list):
                for v in n:
                    find(v)

        find(tree)
        bad = [s for s in stubs if "storageClass" in s]
        fails = []
        if bad:
            fails.append("referencedDecl NOW carries `storageClass` (%d stubs) — the "
                         "pre-pass is no longer the only way to answer, and the "
                         "docstring's measured claim is stale" % len(bad))
        if (st["addr_automatic"], st["addr_static"]) != (2, 1):
            fails.append("&-classification is (automatic=%d, static=%d), expected (2, 1): "
                         "`&loc` and `&prm` are automatic, `&g` is not"
                         % (st["addr_automatic"], st["addr_static"]))
        if fails:
            sys.exit("c_construct_census --selftest FAILED:\n  " + "\n  ".join(fails))
        print("c_construct_census --selftest ok: referencedDecl carries no "
              "storageClass (%d stubs checked); &automatic=2 &static=1" % len(stubs))
        return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("source", nargs="?", help="the C translation unit to census")
    ap.add_argument("--selftest", action="store_true",
                    help="check the frontend facts the census depends on, and exit")
    ap.add_argument("-o", "--output", help="write the census JSON here")
    ap.add_argument("--compare", metavar="JSON",
                    help="print the delta against a previous run and exit")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if not args.source:
        ap.error("a source file is required (or --selftest)")
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
