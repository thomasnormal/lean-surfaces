#!/usr/bin/env python3
"""es_register_check.py — gate the ES tier's DECLARED-DIVERGENCE register.

`docs/family-architecture.md` §5.0a: a divergence the tier has decided to
carry is a DEBT, and debts are registered, aged and gated, never narrated.
This is the gate.

    python3 harness/es_register_check.py
    python3 harness/es_register_check.py --self-test

WHY THIS IS A FILE AND NOT A `python3 -c` IN THE GATE LIST.  It was written
inline first, and `tools/triad.sh` splits `--gates` on `;` WITHOUT respecting
quoting, so a one-liner containing Python semicolons was shredded into five
shell fragments.  Every fragment failed, the triad went RED, and **the
register was never validated at all** — five FAILED lines that tested nothing
about their subject.  A gate spec is code; inline multi-line code in a
`;`-separated list is how that happens.

WHY IT IS TEMPORARY.  `harness/divergence_register.py` is the canonical
checker (pyc's inch-3 branch).  When it merges this file goes away and the
gate becomes `python3 harness/divergence_register.py` — MEAS-28 applies to
inline validators too, and a second copy of a shared instrument is exactly
the duplication that law polices.  Until then a lane-local file is the
smaller wrong.

EXIT CODES (MEAS-40): 0 the register is well formed; 1 a violation; 2 a
refusal (the input is not readable at all).

Python >= 3.9, stdlib only.
"""

import json
import re
import sys
from pathlib import Path

REGISTER = Path(__file__).resolve().parent.parent / "docs" / "es-declared-divergences.json"
SCHEMA = "declared-divergences-0.1"

# §5.0a's six fields, plus the two the ruling's canonical row added.
REQUIRED = ("id", "site", "oracle", "model", "inherited_from",
            "declared", "retirement_condition", "guards", "kind")
KINDS = {"semantic", "observational", "performance"}

# "when someone models it" is not a retirement condition (§9's WAITING rule).
WAITING = re.compile(r"when (someone|somebody|a lane|we) (models?|gets?|implements?)", re.I)


class Violation(Exception):
    pass


def check_register(doc, guard_source):
    """Validate a parsed register.  `guard_source(path)` returns that file's
    text, so the caller decides whether the guards are on disk or in memory —
    which is what lets `--self-test` exercise the failure directions without
    writing files."""
    if doc.get("schema") != SCHEMA:
        raise Violation(f"schema is {doc.get('schema')!r}, expected {SCHEMA!r}")
    rows = doc.get("rows")
    if not isinstance(rows, list):
        raise Violation("`rows` is missing or not a list")
    seen = set()
    for row in rows:
        rid = row.get("id", "<no id>")
        missing = [f for f in REQUIRED if f not in row]
        if missing:
            raise Violation(f"{rid}: missing field(s) {', '.join(missing)}")
        if rid in seen:
            raise Violation(f"{rid}: duplicate id")
        seen.add(rid)
        if row["kind"] not in KINDS:
            raise Violation(f"{rid}: kind {row['kind']!r} is not one of {sorted(KINDS)}")
        if WAITING.search(row["retirement_condition"]):
            raise Violation(
                f"{rid}: retirement condition is a WAITING clause — §9 forbids "
                f"'when someone models it' as a condition")
        # §5.0a's paired-guard law: BOTH directions, and the named guards must
        # actually exist.  A register that names a guard nobody wrote is the
        # unexercised-gate failure one level up.
        guards = row["guards"]
        if not isinstance(guards, list) or len(guards) < 2:
            raise Violation(
                f"{rid}: needs at least TWO guards (still-divergent AND "
                f"has-not-widened); got {guards!r}")
        for g in guards:
            if ":" not in g:
                raise Violation(f"{rid}: guard {g!r} is not `<path>: <name>`")
            path, name = g.split(":", 1)
            name = name.strip()
            try:
                text = guard_source(path.strip())
            except FileNotFoundError:
                raise Violation(f"{rid}: guard file {path.strip()!r} does not exist")
            if not re.search(rf"\b{re.escape(name)}\b", text):
                raise Violation(f"{rid}: guard {name!r} is not defined in {path.strip()}")
    return len(rows)


def _on_disk(path):
    p = Path(__file__).resolve().parent.parent / path
    if not p.is_file():
        raise FileNotFoundError(path)
    return p.read_text(encoding="utf-8")


def self_test():
    """BOTH DIRECTIONS (MEAS-42): the checker must accept a good register AND
    reject each way one can go wrong.  A gate that has only ever been seen to
    pass is the failure this whole file exists because of."""
    good = {
        "schema": SCHEMA,
        "rows": [{
            "id": "x-1", "site": "s", "oracle": "o", "model": "m",
            "inherited_from": "", "declared": "2026-08-24",
            "retirement_condition": "the prologue is parsed",
            "kind": "semantic",
            "guards": ["a.lean: still_divergent", "a.lean: has_not_widened"],
        }]
    }
    src = lambda p: "def still_divergent := true\ndef has_not_widened := true\n"
    assert check_register(good, src) == 1
    print("  ok: a well-formed register passes")

    def rejects(mutate, why):
        import copy
        bad = copy.deepcopy(good)
        mutate(bad)
        try:
            check_register(bad, src)
        except Violation:
            print(f"  ok: rejects {why}")
            return
        raise AssertionError(f"did NOT reject {why}")

    rejects(lambda d: d.update(schema="nope"), "a wrong schema")
    rejects(lambda d: d["rows"][0].pop("kind"), "a missing field")
    rejects(lambda d: d["rows"][0].update(kind="vibes"), "an unknown kind")
    rejects(lambda d: d["rows"][0].update(guards=["a.lean: still_divergent"]),
            "a single guard (the paired-guard law)")
    rejects(lambda d: d["rows"][0].update(
        retirement_condition="when someone models it"), "a WAITING retirement condition")
    rejects(lambda d: d["rows"][0].update(
        guards=["a.lean: nonexistent_guard", "a.lean: has_not_widened"]),
        "a guard that is named but not defined")
    rejects(lambda d: d["rows"].append(d["rows"][0]), "a duplicate id")
    print("  ok: seven failure directions all refuse")
    return 0


def main(argv):
    if argv and argv[0] == "--self-test":
        return self_test()
    if not REGISTER.is_file():
        print(f"REFUSED: {REGISTER} does not exist", file=sys.stderr)
        return 2
    try:
        doc = json.loads(REGISTER.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        print(f"REFUSED: {REGISTER} is not JSON: {e}", file=sys.stderr)
        return 2
    try:
        n = check_register(doc, _on_disk)
    except Violation as e:
        print(f"REGISTER VIOLATION: {e}", file=sys.stderr)
        return 1
    print(f"es declared-divergence register: {n} row(s), all fields present, "
          f"every named guard defined")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
