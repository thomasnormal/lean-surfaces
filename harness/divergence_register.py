#!/usr/bin/env python3
"""divergence_register.py — THE DECLARED-DIVERGENCE REGISTER'S CHECKER.

    python3 harness/divergence_register.py [--json] [--list]

**One shared checker, per-tier data, per-tier probes** (family-architecture
§5.0a, ruled 2026-08-24). The three pieces and why they split where they do:

    DATA     docs/<lang>-declared-divergences.json   -- per tier, one schema
    CHECKER  this file                               -- shared, tier-agnostic
    PROBE    named in each file's `probe` field      -- per tier

**This file asks only questions that are the same for every tier** — does the
row have all its fields, does it name a probe, did the probe run, is it still
divergent, has it widened. MEAS-28 forbids implementing those six times. **The
probe asks the question only the tier can ask**: SV counts claim sites, ES
proves two theorems, the Python tier pins a `GenStatus` constructor. A shared
probe would have to know every tier's semantics, which is the thing tiers exist
to keep separate — so nothing semantic is decided here.

**WHY A DECLARED DIVERGENCE IS NOT A WHITELIST ROW.** `DIVERGE` stays zero,
always; it is a verdict about a run nobody decided in advance. What lives here
is a decision already taken, with a name and an owner — a DEBT, and debts are
registered, aged and gated, never narrated. A whitelist is a permission and it
does not age.

**GATED IN BOTH DIRECTIONS, which is what makes it a ledger and not a list.**
Every row names exactly two guards:

  * `..._still_divergent`  — a divergence that has been silently FIXED leaves a
    stale declaration, and a stale declaration is a false claim about the tier
    that reads as diligence;
  * `..._has_not_widened`  — a divergence that has silently WIDENED is the same
    row describing a bigger fact, which is the worse failure and the one no
    reader notices.

**AND THE GUARD SET IS CHECKED BOTH WAYS TOO.** A row naming a guard the probe
does not define is UNGATED; a probe defining a guard no row names is ORPHANED —
the shape a deleted row leaves behind. Either is an error here, because the one
hole a build cannot see is a row and its guard being removed together.

**THE SCHEMA, WRITTEN DOWN ONCE.** The next tier should read this block, not
infer the shape from a neighbour's file.

    {
      "tier":   "<lang>",                     required
      "schema": "declared-divergences-1",     required (see MIGRATION below)
      "probe":  "harness/<lang>_probe.py",    OPTIONAL - see PROBE SHAPES
      "rows": [ {
        "id":                   "<lang>-div-N",       required
        "kind":                 "semantic"|"provenance",   required
        "site":                 "...",                required
        "oracle":               "...",                required
        "model":                "...",                required
        "inherited_from":       "<cite>" | null,      required KEY; null = ORIGINATED
        "declared":             "YYYY-MM-DD",         required (rows are AGED)
        "retirement_condition": "...",                required, must name an EVENT
        "guards":               [ "<still_divergent>", "<has_not_widened>" ]
      } ]
    }

Any other key is free-form and preserved; tiers use them for `gated`,
`blocked_on`, `why_not_a_refusal`, and so on.

**TWO PROBE SHAPES, both satisfying "named in the row".**

  * SCRIPT (sv, python): the file names `probe`, the checker RUNS it with
    `--json` and reads each guard's `held`. The probe is the run.
  * DECLARATION (es): no `probe` key; each guard is `"<path>: <name>"`, and the
    checker verifies BOTH that `def <name>` is declared there and that a
    `#guard <name>` evaluates it. THE BUILD is the run — a `#guard` that stops
    holding fails the tenure, which is a stronger gate than a script, not a
    weaker one. Both halves are required: a `def` nobody `#guard`s is a guard
    in name only, and a bare substring test passes a name that survives in a
    COMMENT after its declaration was deleted.

**MIGRATION (the §9.5a old-valid clause, applied to schemas).** A shape a lane
shipped in good faith cannot become a failure the day the canon lands. So
`declared-divergences-0.1` is ACCEPTED with a warning, and a blank
`inherited_from` warns rather than fails. Warnings do not change the exit
status; they name what the next normalisation should fix.

Exit status: 0 = every file valid and every guard held; 1 = any defect.
Warnings are reported and do not affect the exit status.
Python 3.9 compatible.
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PATTERN = os.path.join(REPO, "docs", "*-declared-divergences.json")
SCHEMA = "declared-divergences-1"
# Shapes shipped before the canon landed. Accepted with a warning, never a
# failure: see MIGRATION in the module docstring.
LEGACY_SCHEMAS = ("declared-divergences-0.1",)

# The six ruled fields, plus the two the first implementations taught.
REQUIRED_ROW = ("id", "kind", "site", "oracle", "model",
                "inherited_from", "declared", "retirement_condition", "guards")
# `probe` is deliberately NOT required: a tier whose guards are DECLARATIONS
# names them in the row instead, and the build is its run (see PROBE SHAPES).
REQUIRED_TOP = ("tier", "schema", "rows")
KINDS = ("semantic", "provenance")
# §9's WAITING rule: a retirement condition that names no event is not one.
NON_CONDITIONS = re.compile(
    r"when (someone|somebody) (models|fixes|gets|implements)|"
    r"^\s*(tbd|todo|eventually|at some point)\b", re.I)


def _fail(problems, path, msg):
    problems.append("%s: %s" % (os.path.relpath(path, REPO), msg))


def _strip_lean_comments(text):
    # NOTE the r-prefix: this docstring QUOTES a regex, and `\s` in a plain
    # string is an invalid escape -- a DeprecationWarning on 3.9 and a
    # SyntaxWarning on 3.14, emitted on EVERY gate run. Prose that quotes code
    # is still code to the lexer.
    r"""Block/doc comments and line comments out. Anchoring alone is not enough:
    `^\s*def foo` can match inside a `/- ... -/` block, and a name surviving in
    a comment after its declaration was DELETED is precisely the case this
    tightening exists to refuse."""
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def declared_as_guard(text, name):
    """Is `name` DECLARED and CHECKED here? Two anchored facts, both required —
    ES's retired lane-local checker required exactly this pair and it is the
    reason the tightening is worth having:

      * `def <name>`    — the declaration exists at a line start, not in prose;
      * `#guard <name>` — and the build actually EVALUATES it.

    A `def` with no `#guard` is a definition nobody checks, which is a guard in
    name only; a `#guard` with no `def` cannot elaborate. Returns (ok, detail)."""
    code = _strip_lean_comments(text)
    has_def = re.search(r"^[ \t]*(?:private[ \t]+)?def[ \t]+%s\b"
                        % re.escape(name), code, re.M) is not None
    has_guard = re.search(r"^[ \t]*#guard[ \t]+%s\b"
                          % re.escape(name), code, re.M) is not None
    if has_def and has_guard:
        return True, "def + #guard"
    missing = []
    if not has_def:
        missing.append("no `def %s` at a line start" % name)
    if not has_guard:
        missing.append("no `#guard %s`" % name)
    return False, " and ".join(missing)


def _warn(warnings, path, msg):
    warnings.append("%s: %s" % (os.path.relpath(path, REPO), msg))


def check_file(path, problems, warnings=None):
    """Schema + probe + both-direction guard checks for ONE tier's file."""
    if warnings is None:
        warnings = []
    try:
        doc = json.load(open(path))
    except Exception as e:                      # noqa: BLE001 - reported, never hidden
        _fail(problems, path, "not valid JSON: %s" % e)
        return {}

    for k in REQUIRED_TOP:
        if k not in doc:
            _fail(problems, path, "missing top-level field %r" % k)
    sch = doc.get("schema")
    if sch in LEGACY_SCHEMAS:
        _warn(warnings, path, "schema is %r; canonical is %r — accepted during "
              "migration, because a shape a lane shipped in good faith cannot "
              "become a failure the day the canon lands" % (sch, SCHEMA))
    elif sch != SCHEMA:
        _fail(problems, path, "schema is %r, expected %r" % (sch, SCHEMA))
    rows = doc.get("rows") or []
    retired = doc.get("retired_rows") or []
    # §5.0a (2026-08-25): A FILE'S LEGALITY IS DECIDED BY ITS CLAIM, NOT ITS
    # LENGTH. `rows: []` beside a non-empty `retired_rows` is a real and useful
    # claim -- "no LIVE debts, and here is how each one closed" -- so it is
    # LEGAL. Both empty claims nothing at all, and a file that claims nothing
    # should not exist.
    if not rows and not retired:
        _fail(problems, path, "rows: [] AND retired_rows: [] — this file makes "
              "no claim at all. DELETE IT: a tier with no live debts and no "
              "retired ones has no register to keep, and an empty ledger reads "
              "as diligence while asserting nothing (family-architecture §5.0a)")

    named = set()
    for row in rows:
        rid = row.get("id", "<unnamed>")
        for k in REQUIRED_ROW:
            if k not in row:
                _fail(problems, path, "row %s missing field %r" % (rid, k))
        if row.get("kind") not in KINDS:
            _fail(problems, path, "row %s kind is %r, expected one of %s"
                  % (rid, row.get("kind"), " | ".join(KINDS)))
        # inherited_from MAY be null -- that is the heavier ORIGINATED claim --
        # but the KEY must be present, because its absence is indistinguishable
        # from an author who never considered the question.
        if "inherited_from" in row and row["inherited_from"] is not None:
            if not str(row["inherited_from"]).strip():
                _warn(warnings, path, "row %s inherited_from is blank; canonical "
                                      "is null for ORIGINATED (migration warning)" % rid)
        d = str(row.get("declared", ""))
        if not re.match(r"^\d{4}-\d{2}-\d{2}$", d):
            _fail(problems, path, "row %s declared is %r, expected YYYY-MM-DD "
                                  "(the field exists so the row can be AGED)"
                  % (rid, d))
        rc = str(row.get("retirement_condition", ""))
        if not rc.strip():
            _fail(problems, path, "row %s has no retirement condition" % rid)
        elif NON_CONDITIONS.search(rc):
            _fail(problems, path, "row %s retirement condition names no event "
                                  "(%r is the WAITING shape §9 forbids)" % (rid, rc[:60]))
        g = row.get("guards")
        if not isinstance(g, list) or len(g) != 2 or len(set(g)) != 2 \
                or not all(isinstance(x, str) and x.strip() for x in g):
            _fail(problems, path, "row %s guards must be TWO distinct named "
                                  "guards (still_divergent / has_not_widened), got %r"
                  % (rid, g))
        else:
            named.update(g)

    # §5.0a clause 3: every RETIRED row must name a live guard whose EXISTENCE
    # this checker verifies. EXISTENCE, NOT PASSAGE -- and the distinction is
    # the whole design. A retired row's `still_divergent` should now FAIL, and
    # that failure is the signal a retired divergence has come back; asserting
    # it holds would invert the meaning, and asserting nothing would let the
    # guard be deleted with the row and take the watch with it.
    retired_named = set()
    for row in retired:
        rid = row.get("id", "<unnamed>")
        for k in REQUIRED_ROW:
            if k not in row:
                _fail(problems, path, "retired row %s missing field %r" % (rid, k))
        d = str(row.get("retired", ""))
        if not re.match(r"^\d{4}-\d{2}-\d{2}$", d):
            _fail(problems, path, "retired row %s has retired=%r, expected "
                  "YYYY-MM-DD — an archive that cannot be aged is the same "
                  "defect as a ledger that cannot" % (rid, d))
        g = row.get("guards")
        if not isinstance(g, list) or len(g) != 2 or len(set(g)) != 2:
            _fail(problems, path, "retired row %s must still name TWO distinct "
                  "guards: retirement moves the row, it does not end the watch"
                  % rid)
        else:
            retired_named.update(g)

    probe = doc.get("probe")
    probe_src = ""
    if probe and os.path.isfile(os.path.join(REPO, probe)):
        probe_src = open(os.path.join(REPO, probe), encoding="utf-8").read()
    for g in sorted(retired_named):
        if ":" in g:
            gpath, gname = (x.strip() for x in g.split(":", 1))
            full = os.path.join(REPO, gpath)
            ok = os.path.isfile(full) and declared_as_guard(
                open(full, encoding="utf-8").read(), gname)[0]
        else:
            ok = re.search(r"^def[ \t]+%s\b" % re.escape(g), probe_src, re.M) is not None
        if not ok:
            _fail(problems, path, "retired row names guard %r and it DOES NOT "
                  "EXIST — retiring a row moves it to the archive, it does not "
                  "delete its guard: the guard is what would notice the "
                  "divergence coming back" % g)

    if not probe:
        # DECLARATION SHAPE. No probe script: each guard is "<path>: <name>" and
        # THE BUILD is the run — a Lean theorem that stops holding fails the
        # tenure, which is a stronger gate than a script and not a weaker one.
        # What a build CANNOT see is a guard deleted along with its row, so that
        # is exactly what is checked here.
        out = {}
        for g in sorted(named):
            if ":" not in g:
                _fail(problems, path, "no `probe` key, and guard %r is not "
                      "'<path>: <name>' — a row must name either a probe script "
                      "or a declaration" % g)
                continue
            gpath, gname = (x.strip() for x in g.split(":", 1))
            full = os.path.join(REPO, gpath)
            if not os.path.isfile(full):
                _fail(problems, path, "guard %r names a file that does not exist" % g)
                continue
            ok, detail = declared_as_guard(open(full, encoding="utf-8").read(), gname)
            if not ok:
                _fail(problems, path, "guard %r is not a checked declaration in "
                      "%s (%s) — a name that survives only in prose is not a guard"
                      % (gname, gpath, detail))
            else:
                out[gname] = {"held": True,
                              "detail": "%s in %s — the BUILD is the run"
                                        % (detail, gpath)}
        return {"tier": doc.get("tier"), "rows": len(rows), "guards": out}
    ppath = os.path.join(REPO, probe)
    if not os.path.isfile(ppath):
        _fail(problems, path, "probe %r does not exist" % probe)
        return {}

    run = subprocess.run([sys.executable, ppath, "--json"],
                         capture_output=True, text=True, cwd=REPO)
    m = re.search(r"^\{.*?^\}", run.stdout, re.S | re.M)
    if not m:
        _fail(problems, path, "probe %r produced no --json object (exit %d)"
              % (probe, run.returncode))
        return {}
    try:
        results = json.loads(m.group(0))
    except Exception as e:                      # noqa: BLE001
        _fail(problems, path, "probe %r --json is not parseable: %s" % (probe, e))
        return {}

    ran = set(results)
    for name in sorted(named - ran):
        _fail(problems, path, "row names guard %r but the probe never ran it "
                              "— the row is UNGATED" % name)
    for name in sorted(ran - named - retired_named):
        _fail(problems, path, "probe defines guard %r that no row names — "
                              "ORPHANED, the shape a deleted row leaves behind" % name)
    # PASSAGE is asserted for LIVE rows only. A retired row's guard is verified
    # to EXIST above; whether it holds is the tier's signal, not this checker's
    # business -- see clause 3.
    for name in sorted(named & ran):
        if not results[name].get("held"):
            _fail(problems, path, "GUARD FAILED %s: %s"
                  % (name, results[name].get("detail", "")))
    return {"tier": doc.get("tier"), "rows": len(rows), "guards": results}


def self_test():
    """A CHECKER THAT ONLY EVER PASSES IS A CLAIM. Every rule above is
    exercised here against a mutated copy of a real tier file, because the
    rules that matter are the ones that have never fired on real data — and
    the day one of them stops firing, nothing else in the tree would notice.
    Runs no Lean and touches no register file: mutations go to a temp dir."""
    import copy
    import tempfile

    base = sorted(glob.glob(PATTERN))
    if not base:
        print("self-test: no register file to mutate", file=sys.stderr)
        return 1
    good = json.load(open(base[0]))

    def rejects(mutate, label):
        doc = copy.deepcopy(good)
        mutate(doc)
        d = tempfile.mkdtemp()
        path = os.path.join(d, "selftest-declared-divergences.json")
        with open(path, "w") as f:
            json.dump(doc, f)
        problems = []
        check_file(path, problems)
        ok = bool(problems)
        print("  %-34s %s" % (label, "rejected" if ok else "*** ACCEPTED ***"))
        return ok

    def drop_inherited(d):
        del d["rows"][0]["inherited_from"]

    def bad_kind(d):
        d["rows"][0]["kind"] = "cosmetic"

    def one_guard(d):
        d["rows"][0]["guards"] = ["only_one"]

    def unknown_guard(d):
        d["rows"][0]["guards"] = [d["rows"][0]["guards"][0], "no_such_guard"]

    def duplicate_guard(d):
        g = d["rows"][0]["guards"][0]
        d["rows"][0]["guards"] = [g, g]

    def waiting_condition(d):
        d["rows"][0]["retirement_condition"] = "when someone models it"

    def undateable(d):
        d["rows"][0]["declared"] = "soon"

    def empty_rows(d):
        d["rows"] = []

    def wrong_schema(d):
        d["schema"] = SCHEMA + "-x"

    def missing_probe(d):
        d["probe"] = "harness/no_such_probe.py"

    # DECLARATION SHAPE (ES's): no probe key, guards are "<path>: <name>".
    # Exercised here as well as by ES's real file, because the day ES
    # normalises to a script this path would otherwise go ungated.
    def decl_guard_missing_file(d):
        d.pop("probe", None)
        d["rows"][0]["guards"] = ["no/such/file.lean: a_still_divergent",
                                  "no/such/file.lean: a_has_not_widened"]

    def decl_guard_not_declared(d):
        # The target must NOT be this file. A substring existence check is
        # self-referential when pointed at its own source: the first draft of
        # this case named the fake declarations inside `divergence_register.py`
        # and the checker duly FOUND them, passing a file it should have
        # rejected. Caught by the self-test's own expectation, which is the
        # argument for having one.
        d.pop("probe", None)
        d["rows"][0]["guards"] = ["docs/sv-declared-divergences.json: absent_decl_a",
                                  "docs/sv-declared-divergences.json: absent_decl_b"]

    def decl_guard_mention_only(d):
        # THE CASE THE TIGHTENING EXISTS FOR, and it needs no fixture file: this
        # name appears in ES's register JSON as DATA and is declared nowhere.
        # The old substring test returned True for exactly this and passed a
        # file it should have refused — the same shape as the self-referential
        # bug this suite caught earlier, which is why it is pinned here.
        d.pop("probe", None)
        d["rows"][0]["guards"] = [
            "docs/es-declared-divergences.json: es_div_1_still_divergent",
            "docs/es-declared-divergences.json: es_div_1_has_not_widened"]

    def decl_guard_def_without_hash_guard(d):
        # A `def` nobody `#guard`s is a guard in name only: it is declared, so
        # the build compiles it, and nothing ever EVALUATES it.
        d.pop("probe", None)
        d["rows"][0]["guards"] = ["LeanModels/Python/Ast.lean: isBuiltinName",
                                  "LeanModels/Python/Ast.lean: isPyBuiltinName"]

    def decl_guard_unqualified(d):
        d.pop("probe", None)
        d["rows"][0]["guards"] = ["bare_name_a", "bare_name_b"]

    # --- §5.0a's THREE CLAUSES (2026-08-25). Built EXPLICITLY rather than
    # mutated from a neighbour's file: these cases must stay deterministic as
    # tiers come and go, and clause 2 is precisely the one that goes untested
    # if nobody writes a fixture for it -- the empty-container law's lesson.
    ES_GUARDS = "Examples/es/statements/guards.lean"

    def _retired_row(guards):
        return {"id": "selftest-div-1", "kind": "semantic",
                "site": "s", "oracle": "o", "model": "m",
                "inherited_from": None, "declared": "2026-08-01",
                "retired": "2026-08-25",
                "retirement_condition": "the guard stops firing",
                "guards": guards}

    def _doc(rows, retired):
        return {"tier": "selftest", "schema": SCHEMA,
                "rows": rows, "retired_rows": retired}

    def accepts(doc, label):
        d = tempfile.mkdtemp()
        path = os.path.join(d, "selftest-declared-divergences.json")
        with open(path, "w") as f:
            json.dump(doc, f)
        problems = []
        check_file(path, problems, [])
        ok = not problems
        print("  %-34s %s" % (label, "accepted" if ok else "*** REJECTED: %s ***"
                              % (problems[0][:70] if problems else "")))
        return ok

    def rejects_doc(doc, label, needle=None):
        d = tempfile.mkdtemp()
        path = os.path.join(d, "selftest-declared-divergences.json")
        with open(path, "w") as f:
            json.dump(doc, f)
        problems = []
        check_file(path, problems, [])
        ok = bool(problems) and (needle is None
                                 or any(needle in p for p in problems))
        print("  %-34s %s" % (label, "rejected" if ok else "*** ACCEPTED ***"))
        return ok

    live = ["%s: es_div_1_still_divergent" % ES_GUARDS,
            "%s: es_div_1_has_not_widened" % ES_GUARDS]
    if not os.path.isfile(os.path.join(REPO, ES_GUARDS)):
        print("self-test: fixture file %s is gone — update the fixture rather "
              "than skipping the case" % ES_GUARDS, file=sys.stderr)
        return 1

    print("divergence_register --self-test (no Lean, no register file touched)")
    clause_ok = [
        accepts(_doc([], [_retired_row(live)]),
                "clause 1: retired-only is LEGAL"),
        rejects_doc(_doc([], []), "clause 2: both empty ERRORS", "DELETE IT"),
        rejects_doc(_doc([], [_retired_row(
                    ["%s: no_such_guard_a" % ES_GUARDS,
                     "%s: no_such_guard_b" % ES_GUARDS])]),
                    "clause 3: retired guard absent FAILS"),
    ]

    checks = [
        (drop_inherited, "missing inherited_from"),
        (bad_kind, "kind outside the ruled two"),
        (one_guard, "one guard instead of two"),
        (unknown_guard, "row names a guard the probe lacks"),
        (duplicate_guard, "the same guard named twice"),
        (waiting_condition, "WAITING-shaped retirement condition"),
        (undateable, "declared that cannot be aged"),
        (empty_rows, "file filed with no rows"),
        (wrong_schema, "wrong schema version"),
        (missing_probe, "probe that does not exist"),
        (decl_guard_missing_file, "declaration guard, file absent"),
        (decl_guard_not_declared, "declaration guard, name not declared"),
        (decl_guard_unqualified, "no probe and guards unqualified"),
        (decl_guard_mention_only, "declaration guard, name only mentioned"),
        (decl_guard_def_without_hash_guard, "declaration guard, def but no #guard"),
    ]
    failed = [lbl for fn, lbl in checks if not rejects(fn, lbl)]
    failed += ["§5.0a clause case"] * clause_ok.count(False)
    if failed:
        print("\nself-test FAILED: accepted %d bad file(s): %s"
              % (len(failed), ", ".join(failed)), file=sys.stderr)
        return 1
    print("\nself-test: OK — %d defect classes rejected, %d §5.0a clauses honoured"
          % (len(checks), len(clause_ok)))
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--list", action="store_true",
                    help="print the rows and exit (no probes run)")
    ap.add_argument("--self-test", action="store_true",
                    help="exercise this checker's OWN defect detection")
    opts = ap.parse_args(argv)

    if opts.self_test:
        return self_test()

    files = sorted(glob.glob(PATTERN))
    problems = []

    # NON-VACUITY. This check is currently UNREACHABLE -- the sv and python
    # tiers have both filed -- and it is kept precisely because that is a fact
    # about today and not about the design: a checker that passes because it
    # found nothing is the unexercised-gate failure this campaign names, and
    # the check costs one line to keep and a silent green to remove.
    if not files:
        print("divergence_register: NO register files matched %s"
              % os.path.relpath(PATTERN, REPO), file=sys.stderr)
        print("A register checker with no data is vacuous. FAIL.", file=sys.stderr)
        return 1

    if opts.list:
        for f in files:
            doc = json.load(open(f))
            for row in doc.get("rows", []):
                print("%-8s %-12s %-11s declared %s  inherited=%s"
                      % (doc.get("tier"), row.get("id"), row.get("kind"),
                         row.get("declared"),
                         row.get("inherited_from") or "ORIGINATED"))
        return 0

    summary = {}
    warnings = []
    for f in files:
        got = check_file(f, problems, warnings)
        if got:
            summary[got["tier"]] = got

    total_rows = sum(s["rows"] for s in summary.values())
    total_guards = sum(len(s["guards"]) for s in summary.values())
    print("DECLARED-DIVERGENCE REGISTER — %d tier file(s), %d row(s), "
          "%d guard(s) run" % (len(files), total_rows, total_guards))
    for tier in sorted(summary):
        s = summary[tier]
        held = sum(1 for g in s["guards"].values() if g.get("held"))
        print("  %-8s %d row(s), %d/%d guards held"
              % (tier, s["rows"], held, len(s["guards"])))
    for tier in sorted(summary):
        for name in sorted(summary[tier]["guards"]):
            g = summary[tier]["guards"][name]
            print("    %-8s %-28s %-4s %s"
                  % (tier, name, "ok" if g.get("held") else "FAIL",
                     g.get("detail", "")))

    if opts.json:
        print(json.dumps({"files": len(files), "rows": total_rows,
                          "tiers": {t: summary[t]["guards"] for t in summary},
                          "problems": problems}, indent=1, sort_keys=True))

    if warnings:
        # Migration warnings NEVER change the exit status: naming what the next
        # normalisation should fix is the point, and turning it into a failure
        # would punish a lane for having shipped before the canon.
        print("\n%d MIGRATION WARNING(S) — not failures:" % len(warnings))
        for w in warnings:
            print("  " + w)
    if problems:
        print("\n%d PROBLEM(S):" % len(problems), file=sys.stderr)
        for p in problems:
            print("  " + p, file=sys.stderr)
        return 1
    print("\ndivergence_register: OK — every row gated both ways, "
          "declared-divergences: %d%s"
          % (total_rows, " (%d migration warning(s))" % len(warnings) if warnings else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
