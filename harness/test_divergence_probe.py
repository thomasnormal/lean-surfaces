#!/usr/bin/env python3
"""test_divergence_probe.py — THE THREE-STATE POLARITY TABLE, made durable.

    python3 harness/test_divergence_probe.py [<probe.py> ...]

Defaults to every `harness/*_divergence_probe.py`. Runs no Lean and touches no
register file: each probe's guard callables are STUBBED, so this asserts the
probe's own exit-code logic and nothing else.

**WHY THIS FILE EXISTS.** §5.0a clause 3 keeps a retired row's guards alive, and
that inverts their polarity: on a LIVE guard `held=False` gates, while on a
RETIRED guard `held=False` is the archive behaving and `held=True` means the
divergence CAME BACK. Three states, two of which are easy to get right and one
of which had never happened — and the one that had never happened was silent in
two tiers at once until it was stubbed and asserted.

    live      retired    rc   meaning
    ------    -------    --   -------------------------------------------
    pass      not-held    0   healthy archive
    FAIL      not-held    1   a live guard gates, as always
    pass      HELD        1   REGRESSION: the divergence returned

**The third row is the point.** It is the state the archive exists to catch, it
has never occurred in any tier, and a case that has never occurred is exactly
the one no reviewer will notice is missing. Asserting it PROSPECTIVELY is the
empty-container law pointed forwards: do not wait for the event to find out
whether the alarm is wired.

A probe that has not adopted the LIVE/RETIRED partition FAILS here rather than
being skipped — an unpartitioned probe cannot express the table at all.

Python 3.9 compatible.
"""

import glob
import importlib.util
import io
import contextlib
import os
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def load(path):
    spec = importlib.util.spec_from_file_location("probe_under_test", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run_with(mod, live_held, retired_held):
    """Stub every guard and read the probe's own rc. Returns (rc, stdout)."""
    mod.LIVE_GUARDS = {k: (lambda h=live_held: (h, "stub"))
                       for k in mod.LIVE_GUARDS}
    mod.RETIRED_GUARDS = {k: (lambda h=retired_held: (h, "stub"))
                          for k in mod.RETIRED_GUARDS}
    mod.GUARDS = dict(mod.LIVE_GUARDS, **mod.RETIRED_GUARDS)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = mod.main()
    return rc, buf.getvalue()


def check(path):
    name = os.path.basename(path)
    mod = load(path)
    if not hasattr(mod, "LIVE_GUARDS") or not hasattr(mod, "RETIRED_GUARDS"):
        print("  %-30s NOT PARTITIONED — no LIVE_GUARDS/RETIRED_GUARDS; the "
              "polarity table cannot be expressed" % name)
        return False
    if not mod.LIVE_GUARDS:
        print("  %-30s no live guards to stub" % name)
        return False

    ok = True
    rc, _ = run_with(mod, True, False)
    good = (rc == 0)
    ok &= good
    print("  %-30s live=pass retired=not-held  rc=%d  %s" % (name, rc, "ok" if good else "*** want 0 ***"))

    rc, _ = run_with(mod, False, False)
    good = (rc == 1)
    ok &= good
    print("  %-30s live=FAIL retired=not-held  rc=%d  %s" % ("", rc, "ok" if good else "*** want 1 ***"))

    if mod.RETIRED_GUARDS:
        rc, out = run_with(mod, True, True)
        good = (rc == 1) and "REGRESSION" in out
        ok &= good
        print("  %-30s live=pass retired=HELD      rc=%d  %s" % ("", rc,
              "ok (regression alarm rang)" if good else
              "*** want 1 + a REGRESSION line — a returned divergence would be SILENT ***"))
    else:
        # Not a skip: say plainly that the row is unexercised and why.
        print("  %-30s live=pass retired=HELD      n/a  no retired rows yet — "
              "this row starts being asserted the day one is archived" % "")
    return ok


def main(argv=None):
    argv = list(argv if argv is not None else sys.argv[1:])
    # `test_divergence_probe.py` itself ENDS IN `_divergence_probe.py`, so the
    # naive glob matched this file and reported it "NOT PARTITIONED". Third time
    # this family has bitten the register work -- a grep that found its own
    # source, a substring test that found a name in its own fixture, and now a
    # glob that found its own file. AN INSTRUMENT LIVES IN THE SPACE IT
    # SEARCHES, and every pattern it writes must exclude itself on purpose.
    probes = argv or sorted(p for p in glob.glob(
        os.path.join(REPO, "harness", "*_divergence_probe.py"))
        if not os.path.basename(p).startswith("test_"))
    if not probes:
        print("test_divergence_probe: no probes found — nothing asserted, "
              "which is not the same as nothing wrong", file=sys.stderr)
        return 1
    print("THREE-STATE POLARITY TABLE — %d probe(s), no Lean, no register file "
          "touched" % len(probes))
    results = [check(p) for p in probes]
    bad = results.count(False)
    print("\ntest_divergence_probe: %s" %
          ("OK — every probe honours the table" if not bad
           else "FAIL — %d probe(s) do not" % bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
