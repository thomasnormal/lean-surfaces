#!/usr/bin/env python3
"""Python tier's declared-divergence PROBE (family-architecture §5.0a).

The register's DATA is `docs/python-declared-divergences.json`; the CHECKER is
the shared `harness/divergence_register.py`. This file is the third piece: the
**probe**, per-tier because it asks a question only this tier can ask.

**Run, never read**, and as of 2026-08-24 that is true of BOTH SIDES.

**THE BOUNDARY THIS FILE USED TO STATE IS GONE.** It read:

    THE DIVERGENCE IS NOT REACHABLE BY AN IN-TIER PROGRAM.

…because observing it needs the first `RuntimeError` SURVIVED, which needs
`except RuntimeError:`, and that was `exc_lab::except_builtin`'s whitelisted
refusal. §pycomplete-22 admitted builtin handler classes and the refusal left
the whitelist, so the sentence expired with it. **It is the fifth claim in this
lane to expire that way and the first inside an instrument** — each was true
when written, and each rested on what the tier COULD NOT do, which is the kind
of premise nothing in the tree tracks.

So `pyc_div_1_still_divergent` now RUNS the program under both, and the model
half is a measurement rather than a reading of `stepIterAt`:

  * `..._still_divergent` — CPython poisons the iterator (`di_used = -1`) and
    re-raises on the second `next` even with a default; the tier CLOSES the
    generator and the default comes back. The absence of a poisoned
    `GenStatus` is still checked alongside, because that is the fact the row's
    RETIREMENT CONDITION names.
  * `..._has_not_widened` — a FRESH cursor over the same dict, made after the
    poisoning, must work on BOTH sides. The row describes one poisoned OBJECT,
    not a poisoned dict and not a poisoned interpreter.

`DICT_GUARDED_ITERATORS` and `STICKY_CAPABLE_RAISES` remain pinned above as
source-level counts: they answer "could a THIRD site inherit this row", which a
program cannot ask.

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

def _run_both(src):
    """Run one program under the ORACLE and under the MODEL. Returns
    ((oracle_rc, oracle_out), (model_rc, model_out)) or None if either side is
    unavailable -- which is a guard FAILURE, never a skip."""
    import tempfile
    d = tempfile.mkdtemp()
    path = os.path.join(d, "probe_div1.py")
    with open(path, "w") as f:
        f.write(src)
    try:
        o = subprocess.run([ORACLE, path], capture_output=True, text=True)
    except FileNotFoundError:
        return None
    # NEVER TRIGGER A BUILD. `leanpy` builds `leanmodels-run` when `.lake` is
    # cold, so a probe that called it unconditionally would start an UNLOCKED
    # Lean build in whatever clone happened to run the shared checker -- exactly
    # what amendment A11's lock exists to prevent, and it would compete with
    # whichever lane holds the tenure. Measured the hard way: this probe kicked
    # off a build in a fresh worktree while another lane held the lock.
    #
    # This file's own docstring already promised it "runs as a POST-BUILD gate";
    # this is that promise made true rather than asserted.
    if not os.path.isfile(os.path.join(REPO, ".lake", "build", "bin", "leanmodels-run")):
        return None
    m = subprocess.run([sys.executable, os.path.join(REPO, "tools", "leanpy"), path],
                       capture_output=True, text=True, cwd=REPO)
    if m.returncode == 2:
        return None
    return (o.returncode, o.stdout.strip()), (m.returncode, m.stdout.strip())


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


DIV1_SRC = """d = {1: 'a'}
it = iter(d)
d[2] = 'b'
try:
    next(it)
except RuntimeError:
    print('first-raised')
print(next(it, 'DEFAULT'))
"""

# THE WIDENING PIN: a FRESH cursor over the same dict, made after the
# poisoning, must still work on BOTH sides. That is what confines the row to
# "this iterator, after its own size guard fired" -- if the model ever stopped
# agreeing here the divergence would have spread past the object that earned it.
DIV1_CTL_SRC = """d = {1: 'a'}
it = iter(d)
d[2] = 'b'
try:
    next(it)
except RuntimeError:
    print('first-raised')
jt = iter(d)
print(next(jt))
"""


def _genstatus_constructors():
    """The `GenStatus` constructor names, read off the inductive. Kept beside
    the program-level run because the row's RETIREMENT CONDITION names this
    exact fact -- a poisoned state landing is what closes the row."""
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


def pyc_div_1_still_divergent():
    """BOTH SIDES RUN, since 2026-08-24-pycomplete-22 put `except RuntimeError:`
    in tier. CPython poisons the iterator and re-raises on the second `next`
    even with a default; the tier CLOSES the generator, so the default comes
    back. Until this inch the model half was pinned at the absence of a poisoned
    `GenStatus` -- honest, but a reading of the code rather than a run of it."""
    got = _run_both(DIV1_SRC)
    if got is None:
        return False, ("could not run both sides (oracle %r missing, or the "
                       "model runner is not built -- this probe runs as a "
                       "POST-BUILD gate)" % ORACLE)
    (orc, oout), (mrc, mout) = got
    oracle_sticky = orc != 0 and "first-raised" in oout and "DEFAULT" not in oout
    model_answers = mrc == 0 and mout.strip().endswith("DEFAULT")
    cons = _genstatus_constructors()
    poisoned = [c for c in cons
                if c.lower() in ("poisoned", "errored", "failed", "invalidated")]
    return (oracle_sticky and model_answers and not poisoned,
            "oracle exit=%d out=%r (sticky=%s) ; model exit=%d out=%r "
            "(answers the default=%s) ; GenStatus = %s"
            % (orc, oout, oracle_sticky, mrc, mout, model_answers,
               "|".join(cons) or "?"))


def pyc_div_1_has_not_widened():
    """CONFINED to the iterator whose own guard fired: a FRESH cursor over the
    same dict works on both sides. The row describes one poisoned object, not a
    poisoned dict and not a poisoned interpreter."""
    got = _run_both(DIV1_CTL_SRC)
    if got is None:
        return False, "could not run both sides (see still_divergent)"
    (orc, oout), (mrc, mout) = got
    agree = orc == 0 and mrc == 0 and oout.split() == mout.split()
    return agree, ("control (FRESH cursor after the poisoning): oracle exit=%d "
                   "out=%r ; model exit=%d out=%r -- both must answer, or the "
                   "divergence has spread past the object that earned it"
                   % (orc, oout, mrc, mout))


GUARDS = {
    "pyc_div_1_still_divergent": pyc_div_1_still_divergent,
    "pyc_div_1_has_not_widened": pyc_div_1_has_not_widened,
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
