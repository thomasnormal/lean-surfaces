#!/usr/bin/env python3
"""c_suite_census.py — how much of a C test corpus is within the tier's reach?

The C23 goal (`docs/c23-goal.md`) is scored against real test suites. Before
pricing that, this measures the suites: for every test, which AST node kinds
it uses, whether those are inside the rung-0 vocabulary the flagship corpus
fixed, whether it needs the PREPROCESSOR, and whether it needs libc.

    python3 harness/c_suite_census.py <dir-of-.c-files> [-o out.json]
    python3 harness/c_suite_census.py <dir> --vocab docs/c-construct-census.json
    python3 harness/c_suite_census.py <dir> --tags        # c-testsuite .tags files
    python3 harness/c_suite_census.py <dir> --limit 200   # sample a big corpus

WHAT "WITHIN REACH" MEANS, precisely. A test is IN-VOCAB when every AST node
kind it produces is in the reference vocabulary (rung 0 = the 45 kinds
`tools/ctwin/sunfish.c` uses). That is a claim about the SHAPE the ingester
must accept, and nothing more: it is NOT a claim that the semantics would run
the test, because rung 0 has no semantics yet. A test can be in-vocab and
still need a libc the tier does not model. Both facts are reported, and the
charter keeps them apart.

A test clang REJECTS is reported as `parse-error`, never as a small program:
clang emits a PARTIAL AST alongside its diagnostic, and counting that would
be a wrong answer rather than a smaller one. Many suite tests are DESIGNED to
be rejected (diagnostic tests), so this is a category, not a failure.

Python >= 3.9, stdlib only.  Deterministic: sorted output, byte-identical on
a double run.
"""

import argparse
import collections
import json
import os
import re
import subprocess
import sys

PROFILE_FLAGS = ["-std=c23", "-D_FORTIFY_SOURCE=0"]
AST_FLAGS = PROFILE_FLAGS + ["-fsyntax-only", "-Xclang", "-ast-dump=json"]

# Headers a freestanding-ish tier gets for free (C23 §4: the freestanding
# headers declare no functions).  Anything else is a hosted-libc need.
# Attribute nodes clang SYNTHESIZES on declarations of names it knows as
# builtins.  Measured: gcc.c-torture/execute/20000313-1.c writes `void abort
# (void);` and no attribute text at all, yet its AST carries `BuiltinAttr` and
# `NoThrowAttr`.  Counting those as constructs the TEST uses would inflate
# every out-of-vocabulary number with the compiler's own bookkeeping, so the
# census reports the count both ways and says which is which.
SYNTHESIZED_ATTRS = re.compile(r"Attr$")

# The printf family, and which argument carries the format string.
FORMAT_FUNCS = {"printf": 0, "fprintf": 1, "sprintf": 1, "snprintf": 2,
                "dprintf": 1, "vprintf": 0, "puts": 0, "fputs": 0}
# C23 7.23.6.1: a conversion specification is % [flags] [width] [.prec]
# [length] conversion.  Captured in parts so the model can be scoped to the
# parts that ACTUALLY appear rather than to the whole mini-language.
CONV_SPEC = re.compile(
    r"%(?P<flags>[-+ #0]*)"
    r"(?P<width>\*|[0-9]+)?"
    r"(?:\.(?P<prec>\*|[0-9]*))?"
    r"(?P<length>hh|h|ll|l|j|z|t|L|w[0-9]+|wf[0-9]+)?"
    r"(?P<conv>[diouxXeEfFgGaAcspn%])")

FREESTANDING = {
    "float.h", "iso646.h", "limits.h", "stdalign.h", "stdarg.h", "stdbit.h",
    "stdbool.h", "stdckdint.h", "stddef.h", "stdint.h", "stdnoreturn.h",
}


def clang_kinds(path):
    """The AST node kinds a test produces, or a refusal category."""
    out = subprocess.run(["clang"] + AST_FLAGS + [path],
                         capture_output=True, text=True)
    if out.returncode != 0:
        return None, "parse-error"
    if not out.stdout:
        return None, "no-ast"
    try:
        tu = json.loads(out.stdout)
    except json.JSONDecodeError:
        return None, "bad-json"
    kinds = collections.Counter()
    # The libc surface the test actually CALLS -- the number that prices the
    # libc rung.  A header a test includes is not a function it needs.
    externs = set()
    defined = set()
    formats = []
    target = os.path.basename(path)
    state = {"file": None}

    def walk(n):
        for slot in (n.get("loc") or {}, (n.get("range") or {}).get("begin") or {}):
            if isinstance(slot, dict):
                inner = slot.get("expansionLoc") or slot.get("spellingLoc") or slot
                if inner.get("file"):
                    state["file"] = inner["file"]
        mine = state["file"] and os.path.basename(state["file"]) == target
        if n.get("kind") and mine:
            kinds[n["kind"]] += 1
        if n.get("kind") == "FunctionDecl" and n.get("name") \
                and any((c or {}).get("kind") == "CompoundStmt"
                        for c in (n.get("inner") or [])):
            defined.add(n["name"])
        if mine and n.get("kind") == "DeclRefExpr":
            d = n.get("referencedDecl") or {}
            if d.get("kind") == "FunctionDecl" and d.get("name"):
                externs.add(d["name"])
        if mine and n.get("kind") == "CallExpr":
            kids = [c for c in (n.get("inner") or []) if isinstance(c, dict)]
            head = kids[0] if kids else {}
            while head.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
                sub = [c for c in (head.get("inner") or []) if isinstance(c, dict)]
                head = sub[0] if sub else {}
            nm = (head.get("referencedDecl") or {}).get("name")
            idx = FORMAT_FUNCS.get(nm)
            if idx is not None and len(kids) > idx + 1:
                arg = kids[idx + 1]
                while arg.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
                    sub = [c for c in (arg.get("inner") or []) if isinstance(c, dict)]
                    arg = sub[0] if sub else {}
                if arg.get("kind") == "StringLiteral" and arg.get("value"):
                    formats.append((nm, arg["value"]))
        for s in ("inner", "args"):
            for c in n.get(s) or []:
                if isinstance(c, dict):
                    walk(c)
    walk(tu)
    kinds.externs = sorted(externs - defined)
    kinds.formats = formats
    return kinds, "ok"


def source_facts(path):
    """Preprocessor and libc needs, read off the source text."""
    try:
        text = open(path, "r", errors="replace").read()
    except OSError:
        return {}
    includes = re.findall(r'^\s*#\s*include\s*[<"]([^>"]+)', text, re.M)
    directives = re.findall(r'^\s*#\s*(\w+)', text, re.M)
    macros = [d for d in directives if d in
              ("define", "undef", "if", "ifdef", "ifndef", "elif", "else",
               "endif", "include", "pragma", "line", "error", "embed")]
    hosted = sorted({h for h in includes if h not in FREESTANDING})
    return {
        "includes": sorted(set(includes)),
        "hosted_headers": hosted,
        "needs_libc": bool(hosted),
        "directives": sorted(set(directives)),
        # `#include` alone is a translation-phase-4 need; a test that also
        # DEFINES macros or branches on them exercises the preprocessor as a
        # language, which is a different obligation.
        "needs_cpp": bool(set(macros) - {"include"}),
    }


def read_tags(path):
    """c-testsuite ships a `.tags` file beside each test."""
    for suffix in (".tags",):
        p = path + suffix
        if os.path.exists(p):
            return sorted(w for w in open(p).read().split() if w)
    return []


def census(paths, vocab, want_tags):
    rows, kinds_union = [], collections.Counter()
    for p in paths:
        kinds, status = clang_kinds(p)
        row = {"test": os.path.basename(p), "status": status}
        row.update(source_facts(p))
        if want_tags:
            row["tags"] = read_tags(p)
        if kinds is not None:
            kinds_union.update(kinds)
            outside = sorted(set(kinds) - vocab) if vocab else []
            written = [k for k in outside if not SYNTHESIZED_ATTRS.search(k)]
            row["kinds"] = len(kinds)
            row["outside_vocab"] = outside
            row["in_vocab"] = not outside
            # ...and the same question with the compiler's synthesized
            # attribute nodes set aside.  This is the number the rung ladder
            # is priced against, because a rung cannot "add" a construct no
            # test ever wrote.
            row["outside_vocab_written"] = written
            row["in_vocab_written"] = not written
            row["libc_calls"] = getattr(kinds, "externs", [])
            row["format_strings"] = sorted({v for _, v in
                                            getattr(kinds, "formats", [])})
        rows.append(row)
    return rows, kinds_union


def _conversions(ok):
    """Tally the printf conversion machinery the corpus ACTUALLY uses.
    Scoped in parts, because the model has to implement the parts that
    appear -- not the whole of C23 7.23.6.1."""
    conv, flags, length, width, prec = (collections.Counter() for _ in range(5))
    n_specs = 0
    for r in ok:
        for f in r.get("format_strings") or []:
            for m in CONV_SPEC.finditer(f):
                n_specs += 1
                conv[m.group("conv")] += 1
                for ch in (m.group("flags") or ""):
                    flags[ch] += 1
                if m.group("length"):
                    length[m.group("length")] += 1
                if m.group("width"):
                    width["*" if m.group("width") == "*" else "digits"] += 1
                if m.group("prec") is not None:
                    prec["*" if m.group("prec") == "*" else "digits"] += 1
    return {"specs_total": n_specs,
            "conversions": dict(conv.most_common()),
            "flags": dict(flags.most_common()),
            "length_modifiers": dict(length.most_common()),
            "width_forms": dict(width.most_common()),
            "precision_forms": dict(prec.most_common())}


def summarize(rows, kinds_union, vocab):
    ok = [r for r in rows if r["status"] == "ok"]
    invocab = [r for r in ok if r.get("in_vocab")]
    invocab_w = [r for r in ok if r.get("in_vocab_written")]
    freestanding = [r for r in ok if not r.get("needs_libc")]
    both = [r for r in ok if r.get("in_vocab") and not r.get("needs_libc")]
    both_w = [r for r in ok if r.get("in_vocab_written") and not r.get("needs_libc")]
    outside, outside_w = collections.Counter(), collections.Counter()
    for r in ok:
        outside.update(r.get("outside_vocab") or [])
        outside_w.update(r.get("outside_vocab_written") or [])
    return {
        "tests": len(rows),
        "parsed": len(ok),
        "by_status": dict(sorted(collections.Counter(
            r["status"] for r in rows).items())),
        "in_vocab": len(invocab),
        "in_vocab_written": len(invocab_w),
        "needs_cpp": sum(1 for r in ok if r.get("needs_cpp")),
        "needs_libc": sum(1 for r in ok if r.get("needs_libc")),
        "freestanding": len(freestanding),
        "in_vocab_and_freestanding": len(both),
        "in_vocab_written_and_freestanding": len(both_w),
        "kinds_union": len(kinds_union),
        "kinds_outside_vocab": len(set(kinds_union) - vocab) if vocab else None,
        "outside_vocab_by_kind": dict(outside.most_common()),
        "outside_vocab_written_by_kind": dict(outside_w.most_common()),
        "format_conversions": _conversions(ok),
        "libc_calls_by_name": dict(collections.Counter(
            f for r in ok for f in (r.get("libc_calls") or [])).most_common(30)),
        "distinct_libc_calls": len({f for r in ok
                                    for f in (r.get("libc_calls") or [])}),
        "no_libc_calls": sum(1 for r in ok if not r.get("libc_calls")),
        "hosted_headers": dict(collections.Counter(
            h for r in ok for h in (r.get("hosted_headers") or [])).most_common(20)),
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("directory")
    ap.add_argument("-o", "--output")
    ap.add_argument("--vocab", help="a c_construct_census.py JSON whose "
                                    "node_kinds are the reference vocabulary")
    ap.add_argument("--tags", action="store_true",
                    help="read c-testsuite `.tags` files beside each test")
    ap.add_argument("--limit", type=int, help="census only the first N tests "
                                              "(sorted); for very large corpora")
    ap.add_argument("--label", help="a name for this corpus in the output")
    args = ap.parse_args()

    if not os.path.isdir(args.directory):
        sys.exit("c_suite_census: not a directory: %s" % args.directory)
    paths = sorted(os.path.join(dp, f)
                   for dp, _, fs in os.walk(args.directory)
                   for f in fs if f.endswith(".c"))
    if not paths:
        sys.exit("c_suite_census: no .c files under %s" % args.directory)
    sampled = args.limit is not None and args.limit < len(paths)
    total = len(paths)
    if sampled:
        paths = paths[:args.limit]

    vocab = set()
    if args.vocab:
        with open(args.vocab) as fh:
            vocab = set(json.load(fh)["node_kinds"])

    rows, kinds_union = census(paths, vocab, args.tags)
    out = {
        "instrument": "harness/c_suite_census.py",
        "corpus": args.label or os.path.basename(args.directory.rstrip("/")),
        "profile_flags": PROFILE_FLAGS,
        "vocab_source": args.vocab,
        "vocab_size": len(vocab) or None,
        "tests_total": total,
        "tests_censused": len(paths),
        "sampled": sampled,
        "summary": summarize(rows, kinds_union, vocab),
        "kinds_union": dict(sorted(kinds_union.items())),
        "tests": rows,
    }
    text = json.dumps(out, indent=2, sort_keys=True) + "\n"
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text)
        s = out["summary"]
        print("%s: %d tests (%d censused), %d parsed | in-vocab %d (written %d) "
              "| freestanding %d | BOTH %d (written %d)"
              % (out["corpus"], total, len(paths), s["parsed"], s["in_vocab"],
                 s["in_vocab_written"], s["freestanding"],
                 s["in_vocab_and_freestanding"],
                 s["in_vocab_written_and_freestanding"]))
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
