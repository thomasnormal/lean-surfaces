#!/usr/bin/env python3
"""SV tier's declared-divergence PROBE (family-architecture §5.0a).

The register's DATA is `docs/sv-declared-divergences.json`; the CHECKER is
the shared `harness/divergence_register.py`. This file is the third piece:
the **probe**, which is per-tier because it has to ask a question only this
tier can ask.

**Run, never read.** §5.0a's run-not-read rule says a row asserting "the
model does X" on the strength of someone's reading has imported prose into
the schema. Every field this probe backs is measured here, and the row
names these guards so the shared checker can verify they exist and ran.

**Both directions, per the paired-guard law.** For each row:

  * `..._still_divergent`  — has the divergence been SILENTLY FIXED? A stale
    declaration is a false claim about the tier that reads as diligence.
  * `..._has_not_widened`  — is it still the divergence described? The same
    row describing a bigger fact is the worse failure, and the one no
    reader notices.

**What "widened" means for a PROVENANCE divergence.** These rows do not say
the model is wrong; they say a CLAIM is unsupported. Such a divergence
widens when the unsupported claim SPREADS — more sites asserting an
adjudication that never happened — so the widening metric is a count of
claim sites, not a semantic diff.

**Retired rows keep their guards** (§5.0a clause 3, ruled 2026-08-25).
Retirement moves a row to the archive; it does not end the watch. The
shared checker verifies a retired row's guards EXIST and never that they
pass — a retired `still_divergent` is *supposed* to report not-held.

Exit 0 = every LIVE guard held, and every retired row still retired.

Exit 1 = a live guard failed, OR a retired `*_still_divergent` HELD — which
means the divergence CAME BACK. A retired guard reporting not-held is the
healthy state and does not gate (folding that in would pin this probe at
exit 1 forever, and a status that is always red says nothing); a retired
guard reporting `ok` is the alarm the archive exists to raise. The polarity
INVERTS at retirement, which is why the two directions are handled apart.

**And a THIRD close: COULD NOT VERIFY.** A guard whose tree is unreadable
has not held and has not failed -- it has not RUN. That was folded into
`0 matches` until 2026-08-25, so a probe pointed at a cold or partial
clone printed a confident PASS about a tree it never opened. Live guards
now fail CLOSED on it, and the regression alarm reads `is True` rather
than truthiness so an unverified guard can never raise a false one.
"""

import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Pinned at DECLARED time; a change in either direction is a guard failure.
#
# sv-div-2's guards were deleted with its row on 2026-08-24, on the reading
# that "a guard whose row is gone guards nothing". §5.0a clause 3 (ruled
# 2026-08-25) REVERSES that: retirement MOVES a row to the archive, it does
# not end the watch, so a retired row must keep naming two guards and the
# shared checker verifies they EXIST. Restored here -- this lane's deletion
# is exactly what clause 3 was written to catch.
DIV1_CLAIM_SITES = 9      # 'xcelium' mentions in docs/sv-design-m0.md
DIV2_CLAIM_SITES = 10     # 'Xcelium-verified outcomes' in Examples/system-verilog


def _grep_count(pattern, path, flags=""):
    """Count matching LINES under `path`.

    Returns an int when the measurement HAPPENED, and None when it could
    NOT -- a missing path, an unreadable tree, no `grep` on PATH.

    These were the same value (0) until 2026-08-25, so "nothing was
    compared" and "compared, found nothing" were indistinguishable, and
    every guard reading `n <= pin` answered a confident `ok` about a tree
    it had never opened. grep's exit status already separates the two:
    0 = found, 1 = searched and found none, >= 2 = could not search.
    """
    try:
        if os.path.isdir(path):
            out = subprocess.run(
                ["grep", "-r" + flags, "-o", pattern, path, "--include=*.lean"],
                capture_output=True, text=True)
            if out.returncode >= 2:
                return None
            return len([l for l in out.stdout.splitlines() if l.strip()])
        if not os.path.isfile(path):
            return None
        out = subprocess.run(["grep", "-c" + flags, pattern, path],
                             capture_output=True, text=True)
        if out.returncode >= 2:
            return None
        return int(out.stdout.strip() or 0)
    except (OSError, ValueError):
        return None


def sv_div_1_still_divergent():
    """DIV-1 is 'the Xcelium operator table is unverified from any reachable
    host'. It is FIXED when a committed Xcelium fixture exists to diff the
    tables against. So: still divergent iff no such fixture is in the tree."""
    root = os.path.join(REPO, "harness", "sv")
    if not os.path.isdir(root):
        return (None, "COULD NOT VERIFY: %s is not a readable directory "
                      "(os.walk on a missing tree yields nothing, which read "
                      "as '0 found' = still divergent)" % root)
    hits = []
    for dp, _, fs in os.walk(root):
        for f in fs:
            if "xcelium" in f.lower() or "xrun" in f.lower():
                hits.append(os.path.join(dp, f))
    return (len(hits) == 0,
            "no committed Xcelium fixture under harness/sv (%d found)" % len(hits))


def sv_div_1_has_not_widened():
    """Widens if the unsupported Xcelium-verification claim spreads to more
    sites in the design memo."""
    n = _grep_count("xcelium", os.path.join(REPO, "docs", "sv-design-m0.md"), "i")
    if n is None:
        return (None, "COULD NOT VERIFY: docs/sv-design-m0.md could not be searched")
    return (n <= DIV1_CLAIM_SITES,
            "sv-design-m0.md xcelium claim sites: %d (pinned <= %d)"
            % (n, DIV1_CLAIM_SITES))


def sv_div_2_still_divergent():
    """DIV-2 is 'guards claim Xcelium adjudication of stimuli no simulator
    ran'. It RETIRES when the rewording lands, so it is still divergent
    exactly while the phrase survives anywhere.

    RETIRED 2026-08-24, so this guard now reports FAIL — and that is the
    watch working, not breaking. Restored verbatim under §5.0a clause 3:
    the checker verifies it EXISTS, never that it passes. Read its state,
    do not gate on it: while the row stays retired this reads FAIL, and it
    flipping to `ok` is the event worth looking at, because that means the
    phrase came back.
    """
    n = _grep_count("Xcelium-verified outcomes",
                    os.path.join(REPO, "Examples", "system-verilog"))
    if n is None:
        return (None, "COULD NOT VERIFY: Examples/system-verilog could not be searched")
    return (n > 0, "'Xcelium-verified outcomes' sites: %d" % n)


def sv_div_2_has_not_widened():
    """Widens if the claim spreads beyond the sites counted at DECLARED.

    Still meaningful after retirement, and it is the half that stays
    ACTIONABLE: it holds at zero and goes red if the reworded phrasing is
    ever undone past the pin."""
    n = _grep_count("Xcelium-verified outcomes",
                    os.path.join(REPO, "Examples", "system-verilog"))
    if n is None:
        return (None, "COULD NOT VERIFY: Examples/system-verilog could not be searched")
    return (n <= DIV2_CLAIM_SITES,
            "'Xcelium-verified outcomes' sites: %d (pinned <= %d)"
            % (n, DIV2_CLAIM_SITES))


# THE PARTITION, AND WHY THE EXIT CODE READS ONLY HALF OF IT.
#
# A retired row's `still_divergent` SHOULD fail — the divergence is gone.
# Folding that into the exit code would make this probe exit 1 forever, so
# every consumer gating on its status would go permanently red and the red
# would mean nothing. The shared checker already reads `--json` and asserts
# passage for LIVE rows only; the exit code has to say the same thing, or
# "existence, not passage" is true of the checker and false of the probe.
#
# Retired guards still RUN, still PRINT, and still appear in `--json` — the
# checker's orphan test reads that set. Their failure is REPORTED, never
# fatal.
LIVE_GUARDS = {
    "sv_div_1_still_divergent": sv_div_1_still_divergent,
    "sv_div_1_has_not_widened": sv_div_1_has_not_widened,
}

RETIRED_GUARDS = {
    "sv_div_2_still_divergent": sv_div_2_still_divergent,
    "sv_div_2_has_not_widened": sv_div_2_has_not_widened,
}

GUARDS = dict(LIVE_GUARDS, **RETIRED_GUARDS)


def main():
    results, rc = {}, 0
    unverified = []
    for name in sorted(GUARDS):
        held, detail = GUARDS[name]()
        retired = name in RETIRED_GUARDS
        results[name] = {"held": held, "detail": detail, "retired": retired}
        # THREE states, not two. `held is None` means the guard could not
        # MEASURE -- which is not evidence either way and must never be
        # folded into "held" or "not held".
        if held is None:
            status = "?"
            unverified.append(name)
        elif held:
            status = "ok"
        else:
            status = "watch" if retired else "FAIL"
        print("%-28s %-5s %s%s"
              % (name, status, detail, "   [retired row]" if retired else ""))
        # LIVE GUARDS FAIL CLOSED, in both directions: a live guard that did
        # not hold gates, and so does one that could not be checked.
        if not retired and held is not True:
            rc = 1
    watching = sorted(n for n in RETIRED_GUARDS if results[n]["held"] is False)
    if watching:
        print("\n%d retired guard(s) reporting not-held: %s"
              % (len(watching), ", ".join(watching)))
        print("Expected while the row stays retired — REPORTED, not fatal "
              "(§5.0a clause 3: existence, not passage).")

    # AND THE OTHER DIRECTION, WHICH IS THE ONE THE WATCH EXISTS FOR.
    # A retired `*_still_divergent` that HOLDS means the divergence CAME BACK.
    # Reporting that as a cheerful `ok` and exiting 0 would be a watch that
    # cannot raise an alarm — the guard runs, the regression happens, and
    # nothing anywhere goes red. So this direction GATES.
    #
    # It reads `is True` and not truthiness ON PURPOSE: an UNVERIFIED guard
    # must not be able to raise a false alarm. "Could not measure" is not
    # "the divergence returned", and an alarm nobody can trust is worse than
    # no alarm.
    returned = sorted(n for n in RETIRED_GUARDS
                      if n.endswith("_still_divergent")
                      and results[n]["held"] is True)
    if returned:
        rc = 1
        print("\n*** REGRESSION: retired guard(s) %s report DIVERGENT again."
              % ", ".join(returned))
        print("*** The divergence has RETURNED. The row must leave the archive "
              "and go back to `rows` — it is a live debt again.")

    # THE THIRD CLOSE. A probe that could not read what it measures has not
    # passed and has not failed -- it has not RUN, and saying PASS there is
    # the unexercised-gate failure this campaign is named after.
    if unverified:
        rc = 1
        print("\n*** COULD NOT VERIFY: %s" % ", ".join(unverified))
        print("*** The tree these guards measure was not readable. This is "
              "NOT evidence that the divergence is gone, and NOT evidence "
              "that it returned — nothing was compared.")
    if "--json" in sys.argv:
        print(json.dumps(results, indent=1, sort_keys=True))
    verdict = "COULD NOT VERIFY" if unverified else ("PASS" if rc == 0 else "FAIL")
    print("\nsv_divergence_probe: %s" % verdict)
    return rc


if __name__ == "__main__":
    sys.exit(main())
