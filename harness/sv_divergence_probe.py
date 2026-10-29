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

**sv-div-3 was this tier's first SEMANTIC row (declared 2026-10-28) and
RETIRED BY REFUSAL the same day (WP4).** On a self-reading `always_comb`
(`if (c) t = a; y = t; t = b;`) `run2` settled to the body's fixpoint, which
is what Yosys synthesizes, while IEEE 1800-2023 §9.2.2.2.1 and Icarus run the
block once per wake-up and show a stale `t`. Thomas's decision (2026-10-28):
no answer is safe, so such a body is refused, loudly — the always_comb
self-read guard (`LeanModels/Sv/CombGuard2.lean`, applied in `instProcess2`
at every parameter point, so in every `name.sem`; `load_design_sv2` refuses
at the defaults). The row moved to `retired_rows`; its guards stay and
change meaning, as §5.0a clause 3 asks:

  * `sv_div_3_still_divergent` now asks whether the divergence CAME BACK:
    whether a self-reading body can again reach `run2` through `name.sem`.
    It holds (the ALARM, which gates) when any refusal pin is gone — the
    guard hook in `instProcess2`, the fixtures' `agree.lean` pins of
    `load_design_sv2`'s refusal (the `#guard_msgs` error text) and of the
    instantiated loud process, the `cases2.json` loud-refusal rows, or the
    `rbw_guard`/`held_guard` theorems. All present = not-held = healthy.
  * `sv_div_3_has_not_widened` keeps measuring the TOOL SPLIT that justifies
    the refusal, layered as before (§5.0a (b)): the build's hand-built
    `#guard (run2 heldDesign …)`/`rbwDesign` pins still give the settle
    answer, Icarus on the committed SV with the pin's own stimulus still
    gives the declared stale trace, and Yosys `prep; eval` still gives the
    settle answer on every two-state point. Not-held means the split moved
    (the tools converged, or split differently) — a reason to revisit the
    refusal, reported, not fatal, since the row is retired.

`sv_div_3_has_not_widened` needs `iverilog`/`vvp` and `yosys` on PATH;
without them it reports COULD NOT VERIFY, which fails the probe like every
unverified guard (the third close below). `sv_div_3_still_divergent` -- the
alarm -- reads files only.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

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
    # A FIXTURE IS RECORDED DATA, NOT INSTRUMENT CODE (repaired 2026-10-28).
    # The CI readiness probe `harness/sv/xcelium_probe.py` and its unit test
    # (34849ef6, 2026-10-09) only ask whether an Xcelium licence will run a
    # one-line module; they record no operator result. The name test counted
    # them as the fixture, reported the row FIXED, and left the shared
    # register red from that commit on. Source files are not counted; any
    # recorded result file whose name mentions xcelium/xrun still is.
    code = (".py", ".pyc", ".sh")
    hits, skipped = [], []
    for dp, _, fs in os.walk(root):
        if "__pycache__" in dp.split(os.sep):
            continue
        for f in fs:
            if "xcelium" in f.lower() or "xrun" in f.lower():
                (skipped if f.lower().endswith(code) else hits).append(
                    os.path.join(dp, f))
    return (len(hits) == 0,
            "no committed Xcelium fixture under harness/sv (%d found; %d "
            "instrument source file(s) named for Xcelium not counted)"
            % (len(hits), len(skipped)))


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


# ---------------------------------------------------------------------------
# sv-div-3 (KIND=semantic, declared 2026-10-28, RETIRED BY REFUSAL 2026-10-28):
# self-reading always_comb.
#
# Per fixture: the Lean design the build pins `run2` on, the committed SV it is
# tied to, its ports (the fixture's own declaration, needed to build a
# testbench without running Lean), the SETTLE answer the hand-built design
# gives, the STALE trace Icarus shows -- both pinned at DECLARED, a change in
# either is the split changing -- the settle-theorem refusal, and the guard
# theorem that refuses the body at instantiation (WP4).
COMB2_EXAMPLE = os.path.join("LeanModels", "Sv", "Comb2ProcExample.lean")
PARAM2 = os.path.join("LeanModels", "Sv", "Param2.lean")
CASES2 = os.path.join("harness", "sv", "cases2.json")
DIV3_FIXTURES = [
    {"design": "heldDesign", "body": "heldBody", "top": "rbw_held",
     "refusal": "held_refused", "guard": "held_guard",
     "sv": "Examples/system-verilog/sem2/rbw_held/rbw_held.sv",
     "agree": "Examples/system-verilog/sem2/rbw_held/agree.lean",
     "ports": [("c", "in", 1), ("a", "in", 2), ("b", "in", 2), ("y", "out", 2)],
     "settle": lambda v: v["a"] if v["c"] == "1" else v["b"],
     "settle_trace": ["01", "10", "11"],
     "stale_trace": ["01", "01", "11"]},
    {"design": "rbwDesign", "body": "rbwBody", "top": "rbw_comb",
     "refusal": "rbw_refused", "guard": "rbw_guard",
     "sv": "Examples/system-verilog/sem2/rbw_comb/rbw_comb.sv",
     "agree": "Examples/system-verilog/sem2/rbw_comb/agree.lean",
     "ports": [("a", "in", 2), ("y", "out", 2)],
     "settle": lambda v: v["a"],
     "settle_trace": ["00", "01", "10", "11"],
     "stale_trace": ["00", "00", "01", "10"]},
]


def _read(relpath):
    """The file's raw text, or None when unreadable."""
    try:
        with open(os.path.join(REPO, relpath), encoding="utf-8") as fh:
            return fh.read()
    except OSError:
        return None


def _lean_code(relpath):
    """The file with Lean comments removed, or None when unreadable. A pin
    that survives only inside a comment is not a pin (the same rule as the
    shared checker's `declared_as_guard`)."""
    text = _read(relpath)
    if text is None:
        return None
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"--[^\n]*", " ", text)


def _model_pin(code, design):
    """(stimulus, expected y trace) of the build's `#guard (run2 <design> ...)`
    pin, or None when no such pin is declared."""
    m = re.search(
        r"^[ \t]*#guard\s*\(\s*run2\s+%s\s+σ_src\s+\d+\s*\[(?P<stim>.*?)\]\s*\)"
        r"\s*\.toOption\.map\s*\(\s*·\.map\s+fun\s+st\s*=>\s*SvState\.showSignal"
        r"\s+st\s+\"y\"\s*\)\s*==\s*some\s*\[(?P<exp>[^\]]*)\]" % re.escape(design),
        code, re.S | re.M)
    if not m:
        return None
    stim = []
    for cyc in re.findall(r"\[([^\[\]]*)\]", m.group("stim")):
        pairs = re.findall(r'\(\s*"(\w+)"\s*,\s*\.lit\s*"([01xz]+)"\s*\)', cyc)
        if not pairs:
            return None
        stim.append(dict(pairs))
    exp = re.findall(r'"([01xz]+)"', m.group("exp"))
    if not stim or len(stim) != len(exp):
        return None
    return stim, exp


def _agree_link(code, fx):
    """The fixture's agree.lean ties the committed SV to the hand-built design:
    it loads the envelope, and checks that the instantiation has the design's
    declarations and the guard's refusal of the design's body as its process."""
    top, d, b = re.escape(fx["top"]), re.escape(fx["design"]), re.escape(fx["body"])
    needed = [
        r'^[ \t]*load_design_sv2\s+%s\s+from\s+"%s\.json"' % (top, re.escape(fx["sv"])),
        r"d\.decls\.toList\s*==\s*%s\.decls\.toList" % d,
        r"combGuardProc\s+%s\.combWd\s+%s\b" % (d, b),
    ]
    return all(re.search(p, code, re.M) for p in needed)


def _refusal_pinned(raw, code, fx):
    """`load_design_sv2`'s refusal of the fixture is pinned: a `#guard_msgs`
    wraps the load, and its expected error is the guard's refusal."""
    top = re.escape(fx["top"])
    wrapped = re.search(r"^[ \t]*#guard_msgs[^\n]*\bin\s*\n[ \t]*load_design_sv2\s+%s\b"
                        % top, code, re.M)
    text = re.search(r"error:\s*load_design_sv2:\s*'%s\.json'\s*REFUSED[^\n]*"
                     r"`AlwaysComb:self-read`" % re.escape(fx["sv"]), raw)
    return bool(wrapped and text)


def _hook_present():
    """`instProcess2` passes every instantiated always_comb through the guard.
    None when Param2.lean is unreadable."""
    code = _lean_code(PARAM2)
    if code is None:
        return None
    return re.search(r"\|\s*\.alwaysComb\s+b\s*=>\s*combGuardProc\b", code) is not None


def _rows_refuse():
    """{top: refusal kind} of the cases2.json rows of the fixtures, or None."""
    text = _read(CASES2)
    if text is None:
        return None
    try:
        cases = json.loads(text)["cases"]
    except (ValueError, KeyError):
        return None
    return {c.get("top"): c.get("refusal") for c in cases
            if c.get("top") in {fx["top"] for fx in DIV3_FIXTURES}}


_DIV3_CACHE = {}


def _icarus_y(fx, stim):
    """Icarus's y trace on the committed SV under `stim`, through the same
    testbench generator diff_test2 uses. None if Icarus is unavailable or the
    run could not be made."""
    key = ("icarus", fx["top"], json.dumps(stim, sort_keys=True))
    if key in _DIV3_CACHE:
        return _DIV3_CACHE[key]
    result = None
    if shutil.which("iverilog") and shutil.which("vvp"):
        sys.path.insert(0, os.path.join(REPO, "harness", "sv"))
        try:
            import gen_tb2
            case = {"name": "sv_div_3_" + fx["top"],
                    "signals": [p[0] for p in fx["ports"]],
                    "stimulus": stim}
            tb = gen_tb2.generate_tb2(fx["top"], fx["ports"], case)
            work = tempfile.mkdtemp(prefix="sv_div_3_")
            try:
                with open(os.path.join(work, "tb.sv"), "w") as fh:
                    fh.write(tb)
                sim = os.path.join(work, "sim")
                c = subprocess.run(["iverilog", "-g2012", "-o", sim, "tb.sv",
                                    os.path.join(REPO, fx["sv"])],
                                   cwd=work, capture_output=True, text=True)
                if c.returncode == 0:
                    r = subprocess.run(["vvp", sim], cwd=work,
                                       capture_output=True, text=True)
                    ys = [dict(kv.split("=", 1) for kv in ln.split()[2:])["y"]
                          for ln in r.stdout.splitlines() if ln.startswith("CYCLE ")]
                    if r.returncode == 0 and len(ys) == len(stim):
                        result = ys
            finally:
                shutil.rmtree(work, ignore_errors=True)
        except Exception:                       # noqa: BLE001 - reported as unverified
            result = None
        finally:
            sys.path.pop(0)
    _DIV3_CACHE[key] = result
    return result


def _yosys_vs_settle(fx):
    """Yosys `prep; eval` against the settle answer on EVERY two-state input
    point. Returns (mismatches, points) or None if Yosys is unavailable."""
    key = ("yosys", fx["top"])
    if key in _DIV3_CACHE:
        return _DIV3_CACHE[key]
    result = None
    if shutil.which("yosys"):
        ins = [p for p in fx["ports"] if p[1] == "in"]
        width = sum(p[2] for p in ins)
        points = []
        for n in range(2 ** width):
            bits = format(n, "0%db" % width)
            v, at = {}, 0
            for name, _d, w in ins:
                v[name] = bits[at:at + w]
                at += w
            points.append(v)
        script = "read_verilog -sv %s; prep -top %s; " % (
            os.path.join(REPO, fx["sv"]), fx["top"])
        script += " ".join("eval %s -show y;" % " ".join(
            "-set %s %d'b%s" % (k, len(b), b) for k, b in v.items()) for v in points)
        try:
            y = subprocess.run(["yosys", "-p", script], capture_output=True, text=True)
            got = re.findall(r"Eval result: \\y = (\d+)'([01xz]+)\.", y.stdout)
            if y.returncode == 0 and len(got) == len(points):
                bad = []
                for v, (w, b) in zip(points, got):
                    b = (b[0] if b[0] in "xz" else "0") * (int(w) - len(b)) + b
                    if b != fx["settle"](v):
                        bad.append("%s->%s" % (v, b))
                result = (bad, len(points))
        except OSError:
            result = None
    _DIV3_CACHE[key] = result
    return result


def sv_div_3_still_divergent():
    """RETIRED ROW: has the divergence COME BACK -- can a self-reading
    always_comb again reach `run2` through `name.sem`? Held (the alarm) when
    any refusal pin is gone: the guard hook in `instProcess2`, a fixture's
    `load_design_sv2` refusal pin or instantiation link in its agree.lean, a
    `cases2.json` loud-refusal row, or a `*_guard` theorem. Not held (the
    healthy, retired state) when every pin is present."""
    hook = _hook_present()
    rows = _rows_refuse()
    example = _lean_code(COMB2_EXAMPLE)
    if hook is None or rows is None or example is None:
        return None, "COULD NOT VERIFY: Param2.lean, cases2.json or Comb2ProcExample.lean unreadable"
    gone = []
    if not hook:
        gone.append("instProcess2 no longer passes always_comb through combGuardProc")
    for fx in DIV3_FIXTURES:
        raw, code = _read(fx["agree"]), _lean_code(fx["agree"])
        if raw is None or code is None:
            return None, "COULD NOT VERIFY: %s unreadable" % fx["agree"]
        if not _refusal_pinned(raw, code, fx):
            gone.append("%s: load_design_sv2's refusal is not pinned" % fx["top"])
        if not _agree_link(code, fx):
            gone.append("%s: the instantiation link to %s is gone" % (fx["top"], fx["design"]))
        if rows.get(fx["top"]) != "AlwaysComb:self-read":
            gone.append("%s: no cases2.json AlwaysComb:self-read refusal row" % fx["top"])
        if not re.search(r"^[ \t]*theorem\s+%s\b" % re.escape(fx["guard"]), example, re.M):
            gone.append("%s: theorem %s is gone" % (fx["top"], fx["guard"]))
    if gone:
        return True, "REFUSAL PIN(S) GONE -- a self-reading body may reach run2 again: " + "; ".join(gone)
    return False, ("refused at ingestion: guard hook in instProcess2, load_design_sv2 refusal "
                   "pinned and instantiation linked for %s, cases2.json refusal rows, "
                   "rbw_guard/held_guard"
                   % ", ".join(fx["top"] for fx in DIV3_FIXTURES))


def sv_div_3_has_not_widened():
    """RETIRED ROW: is the tool split that justified the refusal still the one
    declared? (1) the build's hand-built `#guard (run2 <design> ...)` pins
    still give the settle answer (what Yosys synthesizes); (2) Icarus on the
    committed SV with the pin's stimulus still gives the declared stale trace;
    (3) Yosys `prep; eval` still gives the settle answer on every two-state
    point; (4) the settle-theorem lowering still refuses both bodies. Not held
    = the split moved -- revisit the refusal (reported, not fatal: the row is
    retired)."""
    code = _lean_code(COMB2_EXAMPLE)
    if code is None:
        return None, "COULD NOT VERIFY: %s is not readable" % COMB2_EXAMPLE
    parts, held = [], True
    for fx in DIV3_FIXTURES:
        pin = _model_pin(code, fx["design"])
        if pin is None:
            return False, ("MODEL PIN GONE: no `#guard (run2 %s ...)` in %s"
                           % (fx["design"], COMB2_EXAMPLE))
        stim, model = pin
        settle = [fx["settle"](v) for v in stim]
        if model != settle or model != fx["settle_trace"]:
            held = False
            parts.append("%s: run2 pin %s is not the declared settle answer %s"
                         % (fx["top"], model, fx["settle_trace"]))
        iv = _icarus_y(fx, stim)
        ys = _yosys_vs_settle(fx)
        if iv is None or ys is None:
            return None, ("COULD NOT VERIFY: %s did not run on %s"
                          % ("Icarus" if iv is None else "Yosys", fx["sv"]))
        if iv != fx["stale_trace"]:
            held = False
            parts.append("%s: Icarus %s is not the declared stale trace %s"
                         % (fx["top"], iv, fx["stale_trace"]))
        bad, n = ys
        if bad:
            held = False
            parts.append("%s: Yosys departs from the settle answer at %d of %d "
                         "points (%s)" % (fx["top"], len(bad), n, ", ".join(bad[:3])))
        if not re.search(r"^[ \t]*theorem\s+%s\s*:\s*%s\.lowerComb\s*=\s*none\b"
                         % (re.escape(fx["refusal"]), re.escape(fx["design"])), code, re.M):
            held = False
            parts.append("%s: the settle-theorem refusal %s is gone" % (fx["top"], fx["refusal"]))
        parts.append("%s: run2 (hand-built) %s vs Icarus %s; Yosys = settle on %d/%d points"
                     % (fx["top"], " ".join(model), " ".join(iv), n - len(bad), n))
    return held, "; ".join(parts)


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
    # sv-div-3 retired by refusal 2026-10-28 (WP4): still_divergent now holds
    # only if a refusal pin is gone (the divergence came back -- the alarm).
    "sv_div_3_still_divergent": sv_div_3_still_divergent,
    "sv_div_3_has_not_widened": sv_div_3_has_not_widened,
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
