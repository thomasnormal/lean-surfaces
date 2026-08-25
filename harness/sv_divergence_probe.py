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

Exit 0 = every LIVE guard held. Exit 1 = a live guard failed (the report
says which). Retired guards run and print, and their state is REPORTED,
never fatal: folding them in would pin this probe at exit 1 forever, and a
status that is always red says nothing.
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
    """Count matching LINES under `path`. Returns an int, never raises."""
    cmd = ["grep", "-rc" + flags, pattern, path]
    if os.path.isdir(path):
        cmd = ["grep", "-r" + flags, "-o", pattern, path, "--include=*.lean"]
        out = subprocess.run(cmd, capture_output=True, text=True)
        return len([l for l in out.stdout.splitlines() if l.strip()])
    out = subprocess.run(["grep", "-c" + flags, pattern, path],
                         capture_output=True, text=True)
    try:
        return int(out.stdout.strip() or 0)
    except ValueError:
        return 0


def sv_div_1_still_divergent():
    """DIV-1 is 'the Xcelium operator table is unverified from any reachable
    host'. It is FIXED when a committed Xcelium fixture exists to diff the
    tables against. So: still divergent iff no such fixture is in the tree."""
    hits = []
    for dp, _, fs in os.walk(os.path.join(REPO, "harness", "sv")):
        for f in fs:
            if "xcelium" in f.lower() or "xrun" in f.lower():
                hits.append(os.path.join(dp, f))
    return (len(hits) == 0,
            "no committed Xcelium fixture under harness/sv (%d found)" % len(hits))


def sv_div_1_has_not_widened():
    """Widens if the unsupported Xcelium-verification claim spreads to more
    sites in the design memo."""
    n = _grep_count("xcelium", os.path.join(REPO, "docs", "sv-design-m0.md"), "i")
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
    return (n > 0, "'Xcelium-verified outcomes' sites: %d" % n)


def sv_div_2_has_not_widened():
    """Widens if the claim spreads beyond the sites counted at DECLARED.

    Still meaningful after retirement, and it is the half that stays
    ACTIONABLE: it holds at zero and goes red if the reworded phrasing is
    ever undone past the pin."""
    n = _grep_count("Xcelium-verified outcomes",
                    os.path.join(REPO, "Examples", "system-verilog"))
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
    for name in sorted(GUARDS):
        held, detail = GUARDS[name]()
        retired = name in RETIRED_GUARDS
        results[name] = {"held": held, "detail": detail, "retired": retired}
        if retired:
            status = "ok" if held else "watch"
        else:
            status = "ok" if held else "FAIL"
        print("%-28s %-5s %s%s"
              % (name, status, detail, "   [retired row]" if retired else ""))
        if not held and not retired:
            rc = 1
    if "--json" in sys.argv:
        print(json.dumps(results, indent=1, sort_keys=True))
    watching = sorted(n for n in RETIRED_GUARDS if not results[n]["held"])
    if watching:
        print("\n%d retired guard(s) reporting not-held: %s"
              % (len(watching), ", ".join(watching)))
        print("Expected while the row stays retired — REPORTED, not fatal "
              "(§5.0a clause 3: existence, not passage).")
    print("\nsv_divergence_probe: %s" % ("PASS" if rc == 0 else "FAIL"))
    return rc


if __name__ == "__main__":
    sys.exit(main())
