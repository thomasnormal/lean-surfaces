#!/usr/bin/env python3
"""C tier's declared-divergence PROBE (family-architecture §5.0a).

The register's DATA is `docs/c-declared-divergences.json`; the CHECKER is the
shared `harness/divergence_register.py`. This file is the third piece: the
probe, which asks the questions only this tier can ask.

**RESTORED, and the deletion it reverses is the point.** `2026-08-25-c-25`
retired this tier's last live row, which left `rows: []`, which the checker
then refused — so the register file AND this probe were deleted as the canon
then read. Arch ruled the other way (`52e9c4b`): a file with `rows: []` and a
non-empty `retired_rows` is **legal and required to stay**, because *"no LIVE
debts — and here is how each one closed"* is a STRONGER claim than a file with
rows, and a retired row keeps its guards because **the guard is what would
notice the divergence coming back.** Both files come back, and the ledger
records the reversal rather than quietly rewriting history.

**BOTH GUARDS OF BOTH ROWS READ A COMMITTED ARTIFACT.**
`docs/c-torture-scoreboard.json` is the §9.0 number written down —
`harness/c_torture_score.py --emit` produces it under the build lock, and it
lists every `failed` test BY NAME because a count cannot say which. So this
probe runs on any machine with no corpus, no toolchain and no lock.

**THE PARTITION (pyc's `dfc65dd`, one shape fleet-wide).** `rc` comes from
LIVE guards only; retired guards run, print and appear in `--json` and their
failure is reported and never fatal — otherwise every retirement would red its
own probe forever, and §5.0a clause 3 asks the checker for a guard's
EXISTENCE, not its passage.

**AND THE ALARM, which is the direction the watch exists for.** A retired
`*_still_divergent` that HOLDS means the divergence CAME BACK. Reporting that
as a cheerful `ok` and exiting 0 would be a watch that cannot raise an alarm.
So that direction GATES. This tier has **no live rows at all**, which makes
the alarm the only thing here that can ever set `rc` — a probe whose entire
job is to notice a return.

Exit 0 = no live guard failed and no retired divergence returned.
"""

import json
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCOREBOARD = os.path.join(REPO, "docs", "c-torture-scoreboard.json")
PIN = os.path.join(REPO, "docs", "c-torture-pin.json")
REGISTER = os.path.join(REPO, "docs", "c-declared-divergences.json")

C_DIV_1_TEST = "20021127-1.c"     # llabs declare-call-define
C_DIV_2_TEST = "20010224-1.c"     # the emptied InitListExpr


def _load(path):
    """The artifact, or None when it is ABSENT OR UNREADABLE.

    A malformed file is the same "nothing was compared" as a missing one, and
    letting `json.load` raise here would turn an unverifiable state into a
    traceback — loud, but a statement about the ENVIRONMENT wearing the costume
    of a crash in the probe.
    """
    if not os.path.isfile(path):
        return None
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except (ValueError, OSError):
        return None


def _failed_tests():
    sb = _load(SCOREBOARD)
    if sb is None:
        return None, None
    return list(sb.get("failed_tests") or []), sb


def c_div_1_still_divergent():
    """Is 20021127-1.c FAILING again?

    POLARITY: this SHOULD read not-held. The row retired by RECLASSIFICATION —
    the test moved out of `failed` into the named `oracle-tests-compiler`
    state, where a conforming semantics must leave it. The model's behaviour
    never changed and never should: it calls the definition and reaches
    `abort()`, which is correct C.

    So `held` here means the test is back in the `failed` column, i.e. the
    reclassification stopped working — a real regression, and the reason this
    guard came back with the row.
    """
    failed, sb = _failed_tests()
    if failed is None:
        return None, ("docs/c-torture-scoreboard.json is absent or unreadable — "
                      "NOTHING WAS COMPARED")
    held = C_DIV_1_TEST in failed
    if held:
        return True, ("%s is in `failed` again — the oracle-tests-compiler "
                      "reclassification is not holding" % C_DIV_1_TEST)
    otc = sorted((sb.get("oracle_tests_compiler_tests") or []))
    return False, ("%s is not in `failed`; it sits in oracle-tests-compiler %r "
                   "as the retirement intended" % (C_DIV_1_TEST, otc))


def c_div_1_has_not_widened():
    """Has the `oracle-tests-compiler` state grown beyond what the PIN names?

    For this row, widening is not a semantic diff — it is the named state
    acquiring members. Membership is by name in `tools/c_corpus_fetch.py` and
    travels in `docs/c-torture-pin.json`; a test entering it without the pin
    changing would be the state being used to move a number, which is the
    failure the named state exists to prevent.
    """
    sb = _load(SCOREBOARD)
    pin = _load(PIN)
    if sb is None or pin is None:
        return None, ("scoreboard or pin absent/unreadable — NOTHING WAS "
                      "COMPARED")
    want = sorted((pin.get("oracle_tests_compiler") or {}).keys())
    got = sorted(sb.get("oracle_tests_compiler_tests") or [])
    return (want == got,
            "oracle-tests-compiler membership pinned=%r scored=%r" % (want, got))


def c_div_2_still_divergent():
    """Is 20010224-1.c FAILING again?

    POLARITY: should read not-held. This row retired on a real FIX — clang's
    JSON dumper puts a partially initialised array's elements under
    `array_filler` and `e_InitListExpr` read only `inner`, so the envelope
    described a different program. `held` means that fix regressed and the
    extractor is emitting empty initializer lists again.
    """
    failed, _ = _failed_tests()
    if failed is None:
        return None, ("docs/c-torture-scoreboard.json is absent or unreadable — "
                      "NOTHING WAS COMPARED")
    held = C_DIV_2_TEST in failed
    if held:
        return True, ("%s is in `failed` again — the array_filler fix in "
                      "extractors/c/extract.py has regressed" % C_DIV_2_TEST)
    return False, "%s is not in `failed`; the extractor fix holds" % C_DIV_2_TEST


def c_div_2_has_not_widened():
    """Is the `failed` column still no larger than the LIVE register rows?

    With zero live rows that reads: **no test may fail at all**. A failing test
    with no row is a divergence nobody declared, and this tier currently
    declares none — so any `failed` at all is either a new debt to write down
    or a regression to fix. Either way it must not pass unnoticed.
    """
    failed, sb = _failed_tests()
    reg = _load(REGISTER)
    if failed is None or reg is None:
        return None, ("scoreboard or register absent/unreadable — NOTHING WAS "
                      "COMPARED")
    live = len(reg.get("rows") or [])
    n = int((sb.get("counts") or {}).get("failed", len(failed)))
    return (n <= live,
            "scoreboard failed=%d, live register rows=%d (pinned <=) %r"
            % (n, live, failed))


# This tier has NO live rows: both are retired. `rc` therefore comes entirely
# from the regression alarm below, which is the honest shape for an archive.
LIVE_GUARDS = {}

# A retired row's `still_divergent` SHOULD fail — the divergence is gone. Its
# failure is REPORTED and does not gate, or every retirement would red its own
# probe forever; the checker verifies these guards EXIST and never asserts they
# pass (§5.0a clause 3). Same partition as `pyc_divergence_probe.py` and
# `sv_divergence_probe.py`, so the shape a fourth tier copies is one shape.
RETIRED_GUARDS = {
    "c_div_1_still_divergent": c_div_1_still_divergent,
    "c_div_1_has_not_widened": c_div_1_has_not_widened,
    "c_div_2_still_divergent": c_div_2_still_divergent,
    "c_div_2_has_not_widened": c_div_2_has_not_widened,
}

GUARDS = dict(LIVE_GUARDS, **RETIRED_GUARDS)


def main():
    rc = 0
    results = {}
    for name in sorted(GUARDS):
        held, detail = GUARDS[name]()
        retired = name in RETIRED_GUARDS
        # THREE STATES, NOT TWO. `held is None` means NOTHING WAS COMPARED --
        # this tier's guards read a COMMITTED artifact, so the unverifiable case
        # is a scoreboard that is missing or malformed. Folding that into False
        # made "the probe could not run" print the same word as "the divergence
        # is gone" -- and with EVERY row here retired, that False also silently
        # disarmed the regression alarm, which is this probe's only job. Live
        # guards fail CLOSED; unverified never passes. (pyc's third state,
        # OPS-148 addendum; one shape fleet-wide.)
        unverified = held is None
        results[name] = {"held": bool(held), "verified": not unverified,
                         "detail": detail, "retired": retired}
        if unverified:
            if not retired:
                rc = 1
        elif not held and not retired:
            rc = 1
        if unverified:
            status = "no-run"
        elif retired:
            status = "ok" if held else "watch"
        else:
            status = "ok" if held else "FAIL"
        print("%-28s %-5s %s%s"
              % (name, status, detail, "   [retired row]" if retired else ""))
    watching = sorted(n for n in RETIRED_GUARDS
                      if results[n]["verified"] and not results[n]["held"])
    if watching:
        print("\n%d retired guard(s) reporting not-held: %s"
              % (len(watching), ", ".join(watching)))
        print("Expected while the row stays retired — REPORTED, not fatal "
              "(§5.0a clause 3: existence, not passage).")

    # AND THE OTHER DIRECTION, WHICH IS THE ONE THE WATCH EXISTS FOR.
    # A retired `*_still_divergent` that HOLDS means the divergence CAME BACK.
    # Reporting that as a cheerful `ok` and exiting 0 would be a watch that
    # cannot raise an alarm. So this direction GATES.
    returned = sorted(n for n in RETIRED_GUARDS
                      if n.endswith("_still_divergent")
                      and results[n]["verified"] and results[n]["held"])
    if returned:
        rc = 1
        print("\n*** REGRESSION: retired guard(s) %s report DIVERGENT again."
              % ", ".join(returned))
        print("*** The divergence has RETURNED. The row must leave the archive "
              "and go back to `rows` — it is a live debt again.")
    if "--json" in sys.argv:
        print(json.dumps(results, indent=1, sort_keys=True))
    unver = sorted(n for n in GUARDS if not results[n]["verified"])
    if unver:
        print("\n%d guard(s) COULD NOT RUN — the committed scoreboard is "
              "absent or unreadable: %s" % (len(unver), ", ".join(unver)))
        print("Nothing was compared, so this says nothing about the model — and "
              "in particular the REGRESSION ALARM did not run. With every row "
              "here retired, an unverified probe is a disarmed one.")
    # AND THE ZERO-LIVE-ROW COROLLARY, which is where the fleet shape's
    # mechanism runs out. "Live guards fail CLOSED" is HOW the shape stops an
    # unverified run counting as a pass -- but this tier has NO live guards, so
    # that clause has nothing to bite on and an unverified probe would exit 0
    # with its regression alarm silently disarmed. The PRINCIPLE is what is
    # fleet-wide, not the mechanism: where there are no live guards, "could not
    # verify" gates directly, because there is nothing else left to.
    if unver and not LIVE_GUARDS:
        rc = 1
    live_fail = [n for n in LIVE_GUARDS
                 if results[n]["verified"] and not results[n]["held"]]
    if rc == 0 and unver:
        verdict = "COULD NOT VERIFY (no comparison ran — not a model verdict)"
    elif rc == 0:
        verdict = "PASS"
    elif live_fail or returned:
        verdict = "FAIL"
    else:
        verdict = "COULD NOT VERIFY (no comparison ran — not a model verdict)"
    print("\nc_divergence_probe: %s" % verdict)
    return rc


if __name__ == "__main__":
    sys.exit(main())
