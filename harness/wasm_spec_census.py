#!/usr/bin/env python3
"""wasm_spec_census.py — census the WebAssembly SPEC's own formal rules.

Run:
    python3 harness/wasm_spec_census.py <path-to-WebAssembly/spec> -o docs/wasm-spec-census.json
    python3 harness/wasm_spec_census.py <path-to-WebAssembly/spec> --compare docs/wasm-spec-census.json
    python3 harness/wasm_spec_census.py <path-to-WebAssembly/spec> --rules wasm-2.0 Step_pure

THIS INSTRUMENT HAS NO SIBLING IN THE C TIER, and that is the point.

C's specification is ISO 9899 prose: `harness/c_construct_census.py` can
census a C *corpus* but there is nothing to census on the *standard's* side
except English. WebAssembly's core spec carries genuine small-step reduction
rules and a typing judgment, AND the working group now maintains them in a
machine-readable DSL -- SpecTec -- under `specification/wasm-{1.0,2.0,3.0}/`
in the spec repository itself, one directory PER VERSION.

So the spec is a censusable artifact. Every rule carries a NAME of the form
`<Relation>/<case>` (e.g. `Step_pure/br_if-true`), and every relation is
declared with its judgment form (`relation Step: config ~> config`). That
makes the surface-to-spec correspondence MECHANICAL rather than editorial:
a Lean surface can be gated on covering a named set, and drift in either
direction is a diff rather than a reading.

The census reports, per version:
  * the declared RELATIONS with their judgment forms, classified into
    validation / reduction / auxiliary by the shape of the judgment;
  * the named RULES per relation -- the mirror obligation, enumerated;
  * `syntax`, `def` and `grammar` declarations, which are the other three
    things a surface has to carry.

Refusal law, unchanged from its siblings: a missing tree, a version
directory with zero `.spectec` files, or a rule whose name does not parse is
an instrument fault and exits non-zero. An empty census is never a finding.

Python >= 3.9, stdlib only.
"""

import argparse
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

SCHEMA = "wasm-spec-census-0.1"

# `rule Step_pure/br_if-true:` / `rule Step/pure:` / `rule Instr_ok/nop:`
RULE_RE = re.compile(r"^rule\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:/\s*([^\s:]+))?\s*:")
# `relation Step: config ~> config    hint(...)`
REL_RE = re.compile(r"^relation\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.*?)\s*(?:hint\(.*)?$")
SYNTAX_RE = re.compile(r"^syntax\s+([A-Za-z_`][A-Za-z0-9_`]*)")
DEF_RE = re.compile(r"^def\s+\$?([A-Za-z_][A-Za-z0-9_]*)")
GRAMMAR_RE = re.compile(r"^grammar\s+([A-Za-z_$][A-Za-z0-9_$]*)")


class Refusal(Exception):
    """A fault in the instrument's input. Never swallowed, never a finding."""


def classify(form):
    """Classify a relation by the SHAPE of its judgment, not by its name.

    The spec's three formal layers each have a distinctive turnstile:
      * validation  `context |- x : t`   -- a typing judgment
      * reduction   `a ~> b` / `a ~>* b` -- small-step, the executable half
      * auxiliary   everything else (subtyping, expansion, constness, …)
    Name-based classification would be a guess; the judgment form is written
    down in the spec and is what the rule actually means."""
    if "~>" in form:
        return "reduction"
    if "|-" in form and ":" in form:
        return "validation"
    return "auxiliary"


def census_version(vdir):
    files = sorted(vdir.glob("*.spectec"), key=lambda p: p.name)
    if not files:
        raise Refusal(f"zero .spectec files under {vdir} -- an empty census is an instrument fault")
    relations = {}
    rules = defaultdict(list)
    syntaxes, defs, grammars = Counter(), Counter(), Counter()
    per_file = {}
    total_lines = 0
    for f in files:
        text = f.read_text(encoding="utf-8", errors="strict")
        nl = text.count("\n")
        total_lines += nl
        fr, fu = 0, 0
        for line in text.splitlines():
            m = REL_RE.match(line)
            if m:
                relations[m.group(1)] = m.group(2).strip()
                fr += 1
                continue
            m = RULE_RE.match(line)
            if m:
                rel, case = m.group(1), m.group(2)
                if case is None:
                    # `rule Foo:` -- a relation with a single unnamed rule.
                    case = "<sole>"
                rules[rel].append(case)
                fu += 1
                continue
            m = SYNTAX_RE.match(line)
            if m:
                syntaxes[m.group(1)] += 1
                continue
            m = DEF_RE.match(line)
            if m:
                defs[m.group(1)] += 1
                continue
            m = GRAMMAR_RE.match(line)
            if m:
                grammars[m.group(1)] += 1
        per_file[f.name] = {"lines": nl, "relations": fr, "rules": fu}

    # A rule naming a relation that was never declared is a parse failure on
    # our side, not a spec defect -- refuse rather than report a wrong table.
    orphans = sorted(set(rules) - set(relations))
    if orphans:
        raise Refusal(f"{vdir.name}: rules for undeclared relations {orphans}")

    kinds = {k: classify(v) for k, v in relations.items()}
    by_kind = Counter(kinds.values())
    rules_by_kind = Counter()
    for rel, cases in rules.items():
        rules_by_kind[kinds[rel]] += len(cases)

    return {
        "version": vdir.name,
        "files": len(files),
        "lines": total_lines,
        "counts": {
            "relations": len(relations),
            "rules": sum(len(v) for v in rules.values()),
            "syntax_decls": len(syntaxes),
            "def_names": len(defs),
            "def_clauses": sum(defs.values()),
            "grammar_names": len(grammars),
            "grammar_clauses": sum(grammars.values()),
        },
        "relations_by_kind": dict(sorted(by_kind.items())),
        "rules_by_kind": dict(sorted(rules_by_kind.items())),
        "relations": {k: {"form": relations[k], "kind": kinds[k],
                          "rules": len(rules.get(k, []))}
                      for k in sorted(relations)},
        "rules": {k: sorted(v) for k, v in sorted(rules.items())},
        "per_file": per_file,
    }


SPLICE_RE = re.compile(r"\$\$\{rule(?:-prose)?:\s*([^}]*)\}")


def splice_check(root, version_rules):
    """Cross-check the census's rule namespace against the PUBLISHED prose.

    `document/core/**/*.rst` -- the spec document itself -- no longer writes
    its rules out; it SPLICES them from SpecTec by name, with directives like

        $${rule: Instr_ok/br_table}
        $${rule-prose: Elemmode_ok/passive Elemmode_ok/declare}

    So the rule names this instrument extracts are the same names the
    published specification cites. That is what makes "one Lean definition
    per spec rule, cited by name" a mechanical correspondence rather than an
    editorial one, and this check is its prototype: EVERY splice pattern must
    resolve to at least one censused rule. A pattern that resolves to nothing
    means the census missed a rule, and is an instrument fault.

    The pattern grammar, recovered by running it: a bare relation name covers
    all that relation's rules, `*` globs, and a bare case name is a GROUP
    PREFIX -- `Step_pure/select` covers `Step_pure/select-true` and
    `Step_pure/select-false`."""
    import fnmatch
    doc = Path(root) / "document" / "core"
    if not doc.is_dir():
        return None
    names = {f"{r}/{c}" for r, cs in version_rules.items() for c in cs}
    pats = set()
    for p in sorted(doc.rglob("*.rst")):
        for m in SPLICE_RE.finditer(p.read_text(encoding="utf-8", errors="replace")):
            for tok in m.group(1).strip().strip("{}").split():
                pats.add(tok.strip("{}"))
    matched, dead = set(), []
    for pat in sorted(pats):
        q = pat if "/" in pat else pat + "/*"
        hit = {n for n in names if fnmatch.fnmatch(n, q)}
        if not hit:
            hit = {n for n in names if fnmatch.fnmatch(n, q + "-*")}
        if hit:
            matched |= hit
        else:
            dead.append(pat)
    return {
        "splice_patterns": len(pats),
        "rules_total": len(names),
        "rules_spliced": len(matched),
        "dead_patterns": dead,
        "never_spliced": sorted(names - matched),
    }


def git_rev(root):
    try:
        r = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"],
                           capture_output=True, text=True, timeout=30)
        if r.returncode == 0:
            return r.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    return None


def git_describe(root):
    try:
        r = subprocess.run(["git", "-C", str(root), "describe", "--tags", "--always"],
                           capture_output=True, text=True, timeout=30)
        if r.returncode == 0:
            return r.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    return None


def census(root):
    root = Path(root).resolve()
    if not root.is_dir():
        raise Refusal(f"not a directory: {root}")
    spec = root / "specification"
    if not spec.is_dir():
        raise Refusal(
            f"no specification/ under {root}. The SpecTec sources moved here "
            f"from spectec/spec/; a checkout predating that move cannot be censused.")
    vdirs = sorted((d for d in spec.iterdir() if d.is_dir()), key=lambda p: p.name)
    if not vdirs:
        raise Refusal(f"no version directories under {spec}")
    versions = {}
    for d in vdirs:
        if not list(d.glob("*.spectec")):
            continue  # e.g. a scratch dir; only refuse if NOTHING has rules
        versions[d.name] = census_version(d)
    if not versions:
        raise Refusal(f"no version directory under {spec} contains .spectec files")

    # Cross-version rule-name deltas: what a surface pinned at one version
    # would have to ADD to reach the next. This is the versioning cost, in
    # the spec's own units.
    names = {v: {f"{rel}/{c}" for rel, cs in d["rules"].items() for c in cs}
             for v, d in versions.items()}
    order = [v for v in ("wasm-1.0", "wasm-2.0", "wasm-3.0", "wasm-latest") if v in names]
    deltas = {}
    for a, b in zip(order, order[1:]):
        deltas[f"{a} -> {b}"] = {
            "added": len(names[b] - names[a]),
            "dropped": len(names[a] - names[b]),
            "kept": len(names[a] & names[b]),
            "dropped_names": sorted(names[a] - names[b]),
        }

    latest = "wasm-latest" if "wasm-latest" in versions else order[-1]
    splices = splice_check(root, versions[latest]["rules"])
    if splices and splices["dead_patterns"]:
        raise Refusal(
            f"{len(splices['dead_patterns'])} splice pattern(s) in document/core "
            f"resolve to no censused rule -- the census MISSED rules: "
            f"{splices['dead_patterns'][:8]}")

    return {
        "schema": SCHEMA,
        "corpus": "WebAssembly/spec specification/ (SpecTec)",
        "revision": git_rev(root),
        "describe": git_describe(root),
        "splice_check": splices,
        "splice_check_version": latest,
        "versions": versions,
        "version_deltas": deltas,
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("spec_root")
    ap.add_argument("-o", "--out")
    ap.add_argument("--compare")
    ap.add_argument("--rules", nargs=2, metavar=("VERSION", "RELATION"),
                    help="print the named rules of one relation")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    try:
        data = census(args.spec_root)
    except Refusal as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2
    except (OSError, UnicodeDecodeError) as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2

    if args.out:
        Path(args.out).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")

    if args.rules:
        v, rel = args.rules
        if v not in data["versions"]:
            print(f"REFUSED: no such version {v}", file=sys.stderr)
            return 2
        d = data["versions"][v]
        if rel not in d["relations"]:
            print(f"REFUSED: no such relation {rel} in {v}", file=sys.stderr)
            return 2
        print(f"{rel} : {d['relations'][rel]['form']}  [{d['relations'][rel]['kind']}]")
        for c in d["rules"].get(rel, []):
            print(f"  {rel}/{c}")
        return 0

    if args.compare:
        old = json.loads(Path(args.compare).read_text(encoding="utf-8"))
        drift = 0
        for v in sorted(set(old["versions"]) | set(data["versions"])):
            a = old["versions"].get(v, {}).get("counts")
            b = data["versions"].get(v, {}).get("counts")
            if a != b:
                print(f"{v}: {a} -> {b}")
                drift += 1
        print("no drift" if not drift else f"{drift} version(s) drifted")
        return 0

    if not args.quiet:
        print(f"{data['corpus']} @ {data['describe']}")
        hdr = f"  {'version':14s} {'files':>5s} {'lines':>6s} {'rels':>5s} {'rules':>6s} " \
              f"{'valid':>6s} {'reduce':>6s} {'aux':>5s} {'syntax':>7s} {'defs':>6s} {'gram':>5s}"
        print(hdr)
        for v, d in data["versions"].items():
            c, rk = d["counts"], d["rules_by_kind"]
            print(f"  {v:14s} {d['files']:5d} {d['lines']:6d} {c['relations']:5d} "
                  f"{c['rules']:6d} {rk.get('validation', 0):6d} {rk.get('reduction', 0):6d} "
                  f"{rk.get('auxiliary', 0):5d} {c['syntax_decls']:7d} "
                  f"{c['def_names']:6d} {c['grammar_names']:5d}")
        print("  version deltas (named rules):")
        for k, d in data["version_deltas"].items():
            print(f"    {k:26s} +{d['added']:4d}  -{d['dropped']:3d}  kept {d['kept']}")
        s = data.get("splice_check")
        if s:
            print(f"  splice check ({data['splice_check_version']}): "
                  f"{s['splice_patterns']} patterns in document/core, "
                  f"{s['rules_spliced']}/{s['rules_total']} rules reached, "
                  f"{len(s['dead_patterns'])} dead, "
                  f"{len(s['never_spliced'])} never spliced")
    return 0


if __name__ == "__main__":
    sys.exit(main())
