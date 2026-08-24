#!/usr/bin/env python3
"""Python tier's declared-divergence PROBE (family-architecture §5.0a).

The register's DATA is `docs/python-declared-divergences.json`; the CHECKER is
the shared `harness/divergence_register.py`. This file is the third piece: the
**probe**, per-tier because it asks a question only this tier can ask.

**Run, never read** — with one boundary this tier has to state plainly, because
stating it is the difference between a measurement and a claim.

    THE DIVERGENCE IS NOT REACHABLE BY AN IN-TIER PROGRAM.

Observing it needs the FIRST `RuntimeError` survived, which needs
`except RuntimeError:` — and `exc_lab::except_builtin` is a whitelisted refusal
(the tier's admitted handler shape names a user-defined class). So there is no
program whose model-side observable is the divergent answer, and a probe that
claimed to have run one would be lying.

**What the guards therefore measure, and why each still fires on the event it
must catch.** The ORACLE half is a genuine run — CPython 3.9.19 executes the
sticky program here, every time. The MODEL half is pinned at the two places the
divergence actually lives, in the shape SV's probe established:

  * `..._still_divergent`  — the model has **no poisoned generator state**.
    `GenStatus` is the whole of it: CPython poisons (`di_used = -1`), the tier
    only ever CLOSES. The retirement condition is precisely "a poisoned state
    is added", so this guard fires on exactly the event that must retire the
    row — a silent fix cannot leave a stale declaration standing.
  * `..._has_not_widened` — the count of SYNTHETIC ITERATOR objects whose frame
    carries a dict guard. Today two: `<enumerate>` (§pycomplete-14) and
    `<iter>` (§pycomplete-18). A third inherits the divergence the day it
    lands, and that is the same row describing a bigger fact.

`<count>` is allocated the same way and is deliberately NOT counted: its frame
carries no dict guard, so it can never raise the sticky error. A widening
metric that counted it would fire on an unrelated feature.

Exit 0 = every guard held. Exit 1 = a guard failed (report says which).
"""

import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ORACLE = os.environ.get("LEANPY_CPYTHON") or "python3.9"

# Pinned at DECLARED time; a change in either direction is a guard failure.
DICT_GUARDED_ITERATORS = 2      # <enumerate>, <iter> -- NOT <count>
STICKY_CAPABLE_RAISES = 4       # dict size-guard raise sites in Monadic/Eval.lean

# The sticky program. It cannot run under the MODEL (`except RuntimeError:` is
# outside the tier); it is the ORACLE's half of the row, run every time.
STICKY_SRC = """
d = {1: 'a'}
it = iter(d)
d[2] = 'b'
try:
    next(it)
except RuntimeError:
    print('first-raised')
print(next(it, 'DEFAULT'))
"""


def _oracle_is_sticky():
    """Run CPython. Sticky means the SECOND `next` re-raises even with a
    default, so the program dies after printing `first-raised`."""
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".py", delete=False) as f:
        f.write(STICKY_SRC)
        path = f.name
    try:
        r = subprocess.run([ORACLE, path], capture_output=True, text=True)
    except FileNotFoundError:
        return None, "oracle %r not installed" % ORACLE
    finally:
        os.unlink(path)
    first = "first-raised" in r.stdout
    died = r.returncode != 0 and "RuntimeError" in r.stderr
    printed_default = "DEFAULT" in r.stdout
    return (first and died and not printed_default,
            "CPython: first next raised=%s, second next re-raised=%s, "
            "answered the default=%s" % (first, died, printed_default))


def _genstatus_constructors():
    """The `GenStatus` constructor names, read off the inductive."""
    src = open(os.path.join(REPO, "LeanModels/Python/Runtime.lean")).read()
    m = re.search(r"inductive GenStatus\b.*?\n((?:.*\n)*?)\s*deriving", src)
    if not m:
        return []
    names = []
    for line in m.group(1).splitlines():
        line = line.strip()
        if line.startswith("|"):
            names += [t for t in re.split(r"[|\s]+", line) if t]
    return names


def _count(pattern, relpath):
    out = subprocess.run(["grep", "-c", pattern, os.path.join(REPO, relpath)],
                         capture_output=True, text=True)
    try:
        return int(out.stdout.strip() or 0)
    except ValueError:
        return 0


def pyc_div_1_still_divergent():
    """Two halves, and BOTH must hold for the row to still be real: CPython
    still poisons, and the model still has nowhere to record a poisoning."""
    sticky, detail = _oracle_is_sticky()
    if sticky is None:
        return False, detail
    cons = _genstatus_constructors()
    poisoned = [c for c in cons
                if c.lower() in ("poisoned", "errored", "failed", "invalidated")]
    return (bool(sticky) and not poisoned,
            "%s; GenStatus = %s (poisoned state present: %s)"
            % (detail, "|".join(cons) or "?", bool(poisoned)))


def pyc_div_1_has_not_widened():
    """The divergence widens by SITE: another synthetic iterator whose frame
    carries a dict guard inherits it the day it lands."""
    ev = "LeanModels/Python/Monadic/Eval.lean"
    src = open(os.path.join(REPO, ev)).read()
    qnames = sorted(set(re.findall(r'heapPush \(\.generator "(<[a-z]+>)"', src)))
    guarded = [q for q in qnames if q in ("<enumerate>", "<iter>")]
    raises = _count('raisePy (\\.runtimeError "dictionary changed size during iteration")', ev)
    ok = (len(guarded) <= DICT_GUARDED_ITERATORS
          and raises <= STICKY_CAPABLE_RAISES)
    return (ok,
            "dict-guarded synthetic iterators: %d %s (pinned <= %d); "
            "sticky-capable raise sites: %d (pinned <= %d); all synthetic: %s"
            % (len(guarded), guarded, DICT_GUARDED_ITERATORS,
               raises, STICKY_CAPABLE_RAISES, qnames))


# --- pyc-div-2: the genexp cursor is created at FIRST RESUME, not at genexp
# construction. PEP 289 evaluates the outermost iterable AND calls iter() on it
# when the genexp object is made, so CPython's snapshot predates a mutation the
# tier's does not see. UNLIKE div-1 this is FULLY REACHABLE in tier, so both
# sides are genuinely RUN here -- the register's first live two-sided probe.
#
# THE WINDOW IS THE WHOLE OF IT, and CTL is what pins that: move the mutation
# to AFTER the first `next` and the tier agrees with CPython again, because by
# then the cursor exists and carries its guards. A row that started describing
# "genexp cursors are wrong" would be describing a bigger fact than the one
# measured.
DIV2_SRC = """d = {1: 'a'}
g = (k for k in d)
d[3] = 'c'
print(next(g))
"""
DIV2_CTL_SRC = """d = {1: 'a', 2: 'b'}
g = (k for k in d)
print(next(g))
d[3] = 'c'
print(next(g))
"""


def _run_both(src):
    """Run one program under the ORACLE and under the MODEL. Returns
    ((oracle_rc, oracle_out), (model_rc, model_out)) or None if the model
    runner is not built -- which is a guard FAILURE, never a skip."""
    import tempfile
    d = tempfile.mkdtemp()
    path = os.path.join(d, "probe_div2.py")
    with open(path, "w") as f:
        f.write(src)
    try:
        o = subprocess.run([ORACLE, path], capture_output=True, text=True)
    except FileNotFoundError:
        return None
    m = subprocess.run([sys.executable, os.path.join(REPO, "tools", "leanpy"), path],
                       capture_output=True, text=True, cwd=REPO)
    if m.returncode == 2:
        return None
    return (o.returncode, o.stdout.strip()), (m.returncode, m.stdout.strip())


def pyc_div_2_still_divergent():
    """CPython RAISES; the tier ANSWERS. Both run, every time."""
    got = _run_both(DIV2_SRC)
    if got is None:
        return False, ("could not run both sides (oracle %r missing, or the "
                       "model runner is not built -- this probe runs as a "
                       "POST-BUILD gate)" % ORACLE)
    (orc, oout), (mrc, mout) = got
    diverges = (orc != 0) and (mrc == 0) and (mout == "1")
    return diverges, ("oracle exit=%d out=%r ; model exit=%d out=%r "
                      "(divergent iff oracle raises and model answers 1)"
                      % (orc, oout, mrc, mout))


def pyc_div_2_has_not_widened():
    """CONFINED to the create-to-first-resume window: with the mutation AFTER
    the first step, the tier agrees with CPython and both raise."""
    got = _run_both(DIV2_CTL_SRC)
    if got is None:
        return False, "could not run both sides (see still_divergent)"
    (orc, oout), (mrc, mout) = got
    agree = (orc != 0) and (mrc != 0) and oout.startswith("1") and mout.startswith("1")
    return agree, ("control (mutation AFTER first next): oracle exit=%d out=%r ; "
                   "model exit=%d out=%r -- both must yield 1 then RAISE, or the "
                   "divergence has widened past the window"
                   % (orc, oout, mrc, mout))


GUARDS = {
    "pyc_div_1_still_divergent": pyc_div_1_still_divergent,
    "pyc_div_1_has_not_widened": pyc_div_1_has_not_widened,
    "pyc_div_2_still_divergent": pyc_div_2_still_divergent,
    "pyc_div_2_has_not_widened": pyc_div_2_has_not_widened,
}


def main():
    rc = 0
    results = {}
    for name in sorted(GUARDS):
        held, detail = GUARDS[name]()
        results[name] = {"held": bool(held), "detail": detail}
        if not held:
            rc = 1
        print("%-28s %-4s  %s" % (name, "ok" if held else "FAIL", detail))
    if "--json" in sys.argv:
        print(json.dumps(results, indent=1, sort_keys=True))
    print("\npyc_divergence_probe: %s" % ("PASS" if rc == 0 else "FAIL"))
    return rc


if __name__ == "__main__":
    sys.exit(main())
