#!/usr/bin/env python3
"""es_m2_census.py — what does an ECMAScript EVALUATOR have to build first?

`harness/es_census.py` measures how big the spec and the suite are.  This
asks the next question, and it is M2's: **given the 66-kind vocabulary M1
ingests, which constructs and which intrinsics does a semantics have to
have before any test can be SCORED, and in what order does building them
clear the most tests?**

    python3 harness/es_m2_census.py --tests <test262> --acorn <acorn.mjs> \
        -o docs/es-m2-census.json
    python3 harness/es_m2_census.py --tests … --acorn … --compare docs/es-m2-census.json
    python3 harness/es_m2_census.py --self-test

THE SEED IS NOT A CHOICE.  Every test262 test runs `harness/assert.js` and
`harness/sta.js` in its realm BEFORE its own source (INTERPRETING.md), so
the prelude's constructs are mandatory for EVERY test, and the ladder below
is seeded with them rather than with something convenient.  A tier that
cannot construct `Test262Error` cannot report a failure, and a tier that
cannot run `assert` cannot report a pass.

THE LADDER is the C lane's `reach_ladder` shape (`docs/c23-goal.md` §4):
greedy, one construct at a time, each step adding the kind that unblocks
the most still-blocked tests.  It prices which constructs to build first;
it is NOT a claim that the semantics would run any test, because at M2's
start there is no semantics.

THE INTRINSIC SURFACE is the ES analogue of the C lane's "the libc
obligation is not libc, it is `printf`" result.  A free identifier — one
the test's own source never binds — must be supplied by the realm, so
counting free identifiers over the slice measures exactly the built-in
surface the evaluator owes.  An unmodeled one is a REFUSE with cause
`unmodeled-intrinsic`, never a language-tier gap.

REFUSAL PATHS (all exercised by --self-test):
  * a missing corpus or acorn        -> exit 2
  * zero tests attributed            -> exit 2 (an empty census is a fault)
  * frontend row count != job count  -> exit 2 (the batch protocol)

Python >= 3.9, stdlib only.  Deterministic: sorted output, byte-identical
on a double run.
"""

import argparse
import collections
import json
import os
import subprocess
import sys
from pathlib import Path

SCHEMA = "es-m2-census-0.1"

HERE = Path(__file__).resolve().parent
DUMPER = HERE.parent / "extractors" / "es" / "estree_dump.mjs"

# Reuse the slice definition rather than restating it: one place decides
# what "the language core" means (docs/es-charter.md §1.5).
sys.path.insert(0, str(HERE))
from es_census import parse_frontmatter, OUT_OF_SLICE_FLAGS, Refusal  # noqa: E402

# The two files INTERPRETING.md makes mandatory in every realm.
PRELUDE = ("assert.js", "sta.js")

# Names that are values rather than realm objects; a tier supplies them by
# existing at all, so they are reported apart from the intrinsic surface.
VALUE_GLOBALS = {"undefined", "NaN", "Infinity", "globalThis", "this"}

def spec_globals(spec_path):
    """The intrinsic list, DERIVED from the pinned spec rather than typed.

    ECMA-262 clause 19 (The Global Object) enumerates the value, function
    and constructor properties of the global object, one `<h1>` each.  So
    "which names must the realm supply?" is a read of the normative text,
    not a list somebody maintained by hand — the same discipline that makes
    the envelope's node table derived rather than chosen.
    """
    import re
    text = Path(spec_path).read_text(encoding="utf-8")
    i = text.find('id="sec-global-object"')
    j = text.find('id="sec-fundamental-objects"')
    if i < 0 or j < 0 or j <= i:
        raise Refusal(f"{spec_path}: cannot locate clause 19 — not an ECMA-262 spec.html?")
    names = set()
    for m in re.finditer(r"<h1>([A-Za-z_$][A-Za-z0-9_$.]*)\s*(?:\(|</h1>)", text[i:j]):
        names.add(m.group(1).split(".")[0])
    if len(names) < 40:
        raise Refusal(f"{spec_path}: clause 19 yielded only {len(names)} names — "
                      f"an implausible global object, so the reader is wrong")
    return names


# Host hooks test262 defines itself (INTERPRETING.md §Host-Defined
# Functions).  These are not ECMA-262 intrinsics and a tier that refuses
# them refuses with cause `environment`, not `unmodeled-intrinsic`.
HOST_DEFINED = {"$262", "print", "$DONOTEVALUATE", "Test262Error",
                "compareArray", "verifyProperty", "assert"}

# Names the PRELUDE itself defines, so a test referencing them needs no
# intrinsic beyond the prelude the realm already ran.
HOST_DEFINED_OK = {"assert", "Test262Error", "$DONOTEVALUATE", "compareArray",
                   "isNegativeZero", "isPrimitive", "formatSimpleValue",
                   "formatIdentityFreeValue"}


def run_dumper(paths, acorn, source_type="auto"):
    if not DUMPER.is_file():
        raise Refusal(f"{DUMPER}: the frontend dumper is missing")
    if not Path(acorn).is_file():
        raise Refusal(f"{acorn}: no acorn there — fetch it and pass --acorn")
    proc = subprocess.run(
        ["node", str(DUMPER), str(acorn), "--source-type", source_type],
        input="\n".join(str(p) for p in paths) + "\n",
        capture_output=True, text=True)
    # "\n" only: `splitlines()` also splits U+2028/U+2029, which test262's
    # line-terminator tests put in their source text.  See §L66's addendum.
    rows = [l for l in proc.stdout.split("\n") if l.strip()]
    if proc.returncode == 3:
        raise Refusal(f"frontend refused: {rows[0] if rows else proc.stderr.strip()}")
    if len(rows) != len(paths):
        raise Refusal(f"frontend returned {len(rows)} rows for {len(paths)} inputs — "
                      f"the batch protocol requires exactly one row per job")
    return [json.loads(r) for r in rows]


def analyse(ast):
    """Node kinds, bound names, referenced names — one walk."""
    kinds = collections.Counter()
    bound = set()
    ids = collections.Counter()
    members = collections.Counter()

    def bind_pattern(p):
        if not isinstance(p, dict):
            return
        t = p.get("type")
        if t == "Identifier":
            bound.add(p["name"])
        elif t == "ObjectPattern":
            for pr in p.get("properties") or []:
                bind_pattern(pr.get("value") if pr.get("type") == "Property" else pr.get("argument"))
        elif t == "ArrayPattern":
            for el in p.get("elements") or []:
                bind_pattern(el)
        elif t in ("AssignmentPattern",):
            bind_pattern(p.get("left"))
        elif t in ("RestElement",):
            bind_pattern(p.get("argument"))

    # Identifier nodes that are NOT references to a binding.  Missing these
    # is how an intrinsic census fills up with `configurable` and `bar`: a
    # non-computed property KEY, a label, and a member NAME are all spelled
    # `Identifier` in ESTree and none of them reads a binding.
    non_ref = set()

    def note_non_refs(n):
        t = n.get("type")
        if t in ("Property", "MethodDefinition", "PropertyDefinition"):
            k = n.get("key") or {}
            if not n.get("computed") and k.get("type") in ("Identifier", "PrivateIdentifier"):
                non_ref.add(id(k))
        elif t == "LabeledStatement":
            if (n.get("label") or {}).get("type") == "Identifier":
                non_ref.add(id(n["label"]))
        elif t in ("BreakStatement", "ContinueStatement"):
            if (n.get("label") or {}).get("type") == "Identifier":
                non_ref.add(id(n["label"]))
        elif t == "MemberExpression" and not n.get("computed"):
            pr = n.get("property") or {}
            if pr.get("type") in ("Identifier", "PrivateIdentifier"):
                non_ref.add(id(pr))
        elif t in ("ImportSpecifier", "ExportSpecifier"):
            for side in ("imported", "exported"):
                s = n.get(side) or {}
                if s.get("type") == "Identifier":
                    non_ref.add(id(s))

    def walk(n):
        if isinstance(n, list):
            for x in n:
                walk(x)
            return
        if not isinstance(n, dict):
            return
        t = n.get("type")
        if isinstance(t, str):
            kinds[t] += 1
            note_non_refs(n)
            if t in ("FunctionDeclaration", "ClassDeclaration") and n.get("id"):
                bound.add(n["id"]["name"])
            if t in ("FunctionDeclaration", "FunctionExpression",
                     "ArrowFunctionExpression"):
                for p in n.get("params") or []:
                    bind_pattern(p)
                if n.get("id"):
                    bound.add(n["id"]["name"])
            if t == "VariableDeclarator":
                bind_pattern(n.get("id"))
            if t == "CatchClause" and n.get("param"):
                bind_pattern(n["param"])
            if t == "Identifier" and id(n) not in non_ref:
                ids[n["name"]] += 1
        for k, v in n.items():
            if k == "type":
                continue
            walk(v)

    # TWO passes: the first marks the non-reference Identifier nodes, the
    # second counts.  One pass cannot work — a key is marked by its PARENT,
    # which `walk` reaches first only by luck of field order.
    walk(ast)          # pass 1: mark the non-reference Identifier nodes
    kinds.clear()      # (pass 1's counts would otherwise be doubled)
    ids.clear()        # (the `id()` marks stay valid: the tree stays alive)
    walk(ast)          # pass 2: count, now that every mark is in place
    free = collections.Counter()
    for name, c in ids.items():
        if name not in bound:
            free[name] = c
    return kinds, free, members


def greedy_ladder(test_kinds, seed, steps=16):
    """At each step add the ONE kind that clears the most blocked tests."""
    built = set(seed)
    cleared = sum(1 for ks in test_kinds if ks <= built)
    out = [{"step": 0, "added": None, "cumulative_cleared": cleared}]
    for i in range(1, steps + 1):
        blocked = [ks for ks in test_kinds if not ks <= built]
        if not blocked:
            break
        gain = collections.Counter()
        for ks in blocked:
            missing = ks - built
            if len(missing) == 1:
                gain[next(iter(missing))] += 1
        if not gain:
            # Nothing clears a test on its own; add the most COMMON missing
            # kind instead, and say so — that is what makes a step honest.
            common = collections.Counter()
            for ks in blocked:
                for k in ks - built:
                    common[k] += 1
            if not common:
                break
            pick, _ = common.most_common(1)[0]
            built.add(pick)
            out.append({"step": i, "added": pick, "clears_alone": 0,
                        "cumulative_cleared": sum(1 for ks in test_kinds if ks <= built)})
            continue
        pick, n = gain.most_common(1)[0]
        built.add(pick)
        out.append({"step": i, "added": pick, "clears_alone": n,
                    "cumulative_cleared": sum(1 for ks in test_kinds if ks <= built)})
    return out, sorted(built)


def census(tests_root, acorn, spec=None):
    globals_ = spec_globals(spec) if spec else None
    root = Path(tests_root)
    testdir = root / "test"
    if not testdir.is_dir():
        raise Refusal(f"{root}: no test/ directory — not a test262 checkout")

    # --- the mandatory prelude, whose kinds seed the ladder
    hdir = root / "harness"
    pre_paths = [hdir / n for n in PRELUDE]
    for p in pre_paths:
        if not p.is_file():
            raise Refusal(f"{p}: the mandatory prelude file is missing")
    pre_rows = run_dumper(pre_paths, acorn, "script")
    seed = set()
    pre_free = collections.Counter()
    pre_detail = {}
    for p, r in zip(pre_paths, pre_rows):
        if not r.get("ok"):
            raise Refusal(f"{p}: the prelude does not parse: {r.get('error')}")
        k, f, _ = analyse(r["ast"])
        seed |= set(k)
        pre_free.update(f)
        pre_detail[p.name] = {"nodes": sum(k.values()), "kinds": sorted(k)}

    # --- the language-core slice
    rows = []
    for p in sorted((testdir / "language").rglob("*.js")):
        if "_FIXTURE" in p.name:
            continue
        parts = p.relative_to(testdir).parts
        if len(parts) > 1 and parts[1] in ("module-code", "import", "export"):
            continue
        meta = parse_frontmatter(p.read_text(encoding="utf-8", errors="strict"), str(p))
        if meta is None:
            continue
        meta.pop("_dedented", None)
        flags = meta.get("flags") or []
        if isinstance(flags, str):
            flags = [flags] if flags else []
        if set(flags) & OUT_OF_SLICE_FLAGS:
            continue
        neg = meta.get("negative")
        inc = meta.get("includes") or []
        if isinstance(inc, str):
            inc = [inc] if inc else []
        rows.append((p, isinstance(neg, dict) and neg.get("phase") == "parse", inc))
    if not rows:
        raise Refusal(f"{testdir}: zero slice files attributed — an instrument fault")

    dump = run_dumper([p for p, _, _ in rows], acorn)

    test_kinds = []
    test_free = []
    free_total = collections.Counter()
    free_tests = collections.Counter()
    includes = collections.Counter()
    parse_neg = 0
    unparsed = 0
    prelude_only = 0
    no_extra_includes = 0
    for (p, expects_err, inc), r in zip(rows, dump):
        for i in inc:
            includes[i] += 1
        if not inc:
            no_extra_includes += 1
        if not r.get("ok"):
            unparsed += 1
            if expects_err:
                parse_neg += 1
            continue
        k, f, _ = analyse(r["ast"])
        ks = set(k)
        test_kinds.append(ks)
        test_free.append(set(f) - HOST_DEFINED_OK)
        if ks <= seed:
            prelude_only += 1
        for name, c in f.items():
            free_total[name] += c
            free_tests[name] += 1

    ladder, built = greedy_ladder(test_kinds, seed)

    # THE RUNG-0 CROSSING.  A test is scoreable only if the evaluator has
    # BOTH its syntax and the realm names it reaches.  Counting either alone
    # overstates the target, so the rung-0 number is the intersection, and
    # it is reported at several intrinsic budgets so the ladder's first step
    # is priced rather than guessed.
    budgets = {
        "none": set(),
        "errors-only": {"Test262Error", "TypeError", "ReferenceError", "SyntaxError",
                        "RangeError", "Error", "EvalError", "URIError"},
        "errors+Object": {"Test262Error", "TypeError", "ReferenceError", "SyntaxError",
                          "RangeError", "Error", "EvalError", "URIError", "Object"},
        "errors+Object+String+Array+Number+Boolean":
            {"Test262Error", "TypeError", "ReferenceError", "SyntaxError", "RangeError",
             "Error", "EvalError", "URIError", "Object", "String", "Array", "Number",
             "Boolean"},
    }
    # value globals are supplied by existing, not by being modeled objects
    freebies = set(VALUE_GLOBALS)
    crossing = {}
    for label, budget in budgets.items():
        allowed = budget | freebies
        n_syntax_only = 0
        n_both = 0
        for ks, fs in zip(test_kinds, test_free):
            syn = ks <= seed
            if syn:
                n_syntax_only += 1
                if set(fs) <= allowed:
                    n_both += 1
        crossing[label] = {"intrinsics_allowed": sorted(budget),
                           "tests_in_prelude_vocabulary": n_syntax_only,
                           "AND_within_the_budget": n_both}

    # A free identifier in this corpus is one of THREE things, and only one
    # of them is a built-in.  Pooling them is how `unresolvableReference`
    # ends up ranked beside `Object`.
    intrinsics, unresolvable, language = {}, {}, {}
    for n, c in free_tests.items():
        if n in HOST_DEFINED:
            continue                       # test262's own harness bindings
        if n == "arguments":
            language[n] = c                # a language binding, not a realm object
        elif globals_ is None or n in globals_:
            intrinsics[n] = c
        else:
            # In a CONFORMANCE suite an unbound name is usually the subject
            # of the test: a deliberate ReferenceError probe.
            unresolvable[n] = c
    return {
        "schema": SCHEMA,
        "prelude": {
            "files": list(PRELUDE),
            "seed_kinds": sorted(seed),
            "seed_size": len(seed),
            "per_file": pre_detail,
            "free_identifiers": dict(sorted(pre_free.items())),
        },
        "slice": {
            "tests": len(rows),
            "parsed": len(test_kinds),
            "did_not_parse": unparsed,
            "of_which_parse_negative": parse_neg,
            "no_extra_includes": no_extra_includes,
            "runnable_with_prelude_vocabulary_only": prelude_only,
        },
        "includes": [[k, v] for k, v in sorted(includes.items(),
                                              key=lambda kv: (-kv[1], kv[0]))],
        "rung0_crossing": crossing,
        "ladder": ladder,
        "ladder_final_vocabulary": built,
        "intrinsic_surface": {
            "source": "ECMA-262 clause 19, read from the pinned spec" if globals_
                      else "NOT spec-derived (--spec was not given)",
            "spec_global_names": len(globals_) if globals_ else None,
            "distinct_referenced": len(intrinsics),
            # A RANKING must be a list: `json.dumps(sort_keys=True)` would
            # re-sort a dict alphabetically and silently destroy the order
            # that is the whole point of the row.
            "by_tests_referencing": [[k, v] for k, v in
                                     sorted(intrinsics.items(), key=lambda kv: (-kv[1], kv[0]))],
            "not_referenced_by_the_slice": sorted(set(globals_) - set(intrinsics))
                                           if globals_ else [],
        },
        "deliberately_unresolvable": {
            "distinct": len(unresolvable),
            "tests_touching_the_top_name": max(unresolvable.values()) if unresolvable else 0,
            "top": [[k, v] for k, v in sorted(unresolvable.items(),
                                              key=lambda kv: (-kv[1], kv[0]))[:12]],
        },
        "language_bindings": language,
        "value_globals_referenced": {n: free_tests[n] for n in sorted(VALUE_GLOBALS)
                                     if n in free_tests},
    }


def self_test():
    import tempfile
    ok = []
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        try:
            census(d, "/nonexistent/acorn.mjs")
            print("SELF-TEST FAIL: a missing corpus did not refuse"); return 1
        except Refusal:
            ok.append("a missing corpus refuses")
        (d / "test").mkdir()
        (d / "harness").mkdir()
        try:
            census(d, "/nonexistent/acorn.mjs")
            print("SELF-TEST FAIL: a missing prelude did not refuse"); return 1
        except Refusal:
            ok.append("a missing prelude refuses")
    # the ladder, on a fixture whose answer is known by hand
    tk = [{"A"}, {"A", "B"}, {"A", "B", "C"}, {"A", "C"}]
    lad, built = greedy_ladder(tk, {"A"})
    assert lad[0]["cumulative_cleared"] == 1, lad
    assert lad[1]["added"] in ("B", "C"), lad
    assert lad[-1]["cumulative_cleared"] == 4, lad
    ok.append("the greedy ladder clears a hand-checked fixture")

    # The non-reference classification, on a fixture built to break the
    # naive version: an object-literal KEY, a label, and a member NAME are
    # all `Identifier` and none of them reads a binding.  The first version
    # of this instrument counted all three and reported `configurable` as
    # the 24th most-used "intrinsic".
    fixture = {"type": "Program", "body": [
        {"type": "LabeledStatement", "label": {"type": "Identifier", "name": "myLabel"},
         "body": {"type": "ExpressionStatement", "expression": {
             "type": "ObjectExpression", "properties": [
                 {"type": "Property", "computed": False,
                  "key": {"type": "Identifier", "name": "configurable"},
                  "value": {"type": "MemberExpression", "computed": False,
                            "object": {"type": "Identifier", "name": "Object"},
                            "property": {"type": "Identifier", "name": "freeze"}}}]}}}]}
    _, free, _ = analyse(fixture)
    assert set(free) == {"Object"}, f"expected only Object to be free, got {dict(free)}"
    ok.append("keys, labels and member names are NOT counted as intrinsics")
    for line in ok:
        print("  ok:", line)
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--tests", help="a test262 checkout")
    ap.add_argument("--spec", help="the pinned spec.html; makes the intrinsic "
                                   "list SPEC-DERIVED rather than assumed")
    ap.add_argument("--acorn", help="a fetched acorn ESM entry point")
    ap.add_argument("-o", "--out")
    ap.add_argument("--compare")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not (args.tests and args.acorn):
        ap.error("--tests and --acorn are required")
    try:
        result = census(args.tests, args.acorn, args.spec)
    except Refusal as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2

    blob = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.compare:
        old = Path(args.compare).read_text(encoding="utf-8")
        if old == blob:
            print(f"{args.compare}: unchanged")
            return 0
        print(f"{args.compare}: DRIFT — re-run with -o to update", file=sys.stderr)
        return 1
    if args.out:
        Path(args.out).write_text(blob, encoding="utf-8")
        print(f"wrote {args.out}")
    else:
        sys.stdout.write(blob)
    return 0


if __name__ == "__main__":
    sys.exit(main())
