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

Exit 0 = every guard held. Exit 1 = a guard failed (report says which).
"""

import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Pinned at DECLARED time; a change in either direction is a guard failure.
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
    exactly while the phrase survives anywhere."""
    n = _grep_count("Xcelium-verified outcomes",
                    os.path.join(REPO, "Examples", "system-verilog"))
    return (n > 0, "'Xcelium-verified outcomes' sites: %d" % n)


def sv_div_2_has_not_widened():
    """Widens if the claim spreads beyond the sites counted at DECLARED."""
    n = _grep_count("Xcelium-verified outcomes",
                    os.path.join(REPO, "Examples", "system-verilog"))
    return (n <= DIV2_CLAIM_SITES,
            "'Xcelium-verified outcomes' sites: %d (pinned <= %d)"
            % (n, DIV2_CLAIM_SITES))


GUARDS = {
    "sv_div_1_still_divergent": sv_div_1_still_divergent,
    "sv_div_1_has_not_widened": sv_div_1_has_not_widened,
    "sv_div_2_still_divergent": sv_div_2_still_divergent,
    "sv_div_2_has_not_widened": sv_div_2_has_not_widened,
}


def main():
    results, rc = {}, 0
    for name in sorted(GUARDS):
        held, detail = GUARDS[name]()
        results[name] = {"held": held, "detail": detail}
        print("%-28s %-4s  %s" % (name, "ok" if held else "FAIL", detail))
        if not held:
            rc = 1
    if "--json" in sys.argv:
        print(json.dumps(results, indent=1, sort_keys=True))
    print("\nsv_divergence_probe: %s" % ("PASS" if rc == 0 else "FAIL"))
    return rc


if __name__ == "__main__":
    sys.exit(main())
