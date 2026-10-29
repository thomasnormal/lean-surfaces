#!/usr/bin/env python3
"""SV phase-2 (semantic tier) differential harness: `run2` vs real simulators.

The sv-0.2 twin of diff_test.py. Per case in harness/sv/cases2.json:

  1. run the Lean side FIRST (`lake env lean --run harness/sv/runner2.lean`):
     it parses the symbolic envelope, replays the crossCheck gate,
     instantiates `Design2` at the case's parameter values, reports the
     elaborated `PORT` widths (the TB's single source of truth) and the
     `CYCLE` trace under σ;
  2. generate a testbench (gen_tb2.py) against the DUT's real source file
     (`Examples/system-verilog/<example>/<top>.sv`) with the case's
     parameter overrides, run it under the selected simulator(s);
  3. diff CYCLE lines. A case passes iff every exercised simulator's trace
     equals the Lean trace for some schedule in `accept_sigmas`
     (default: `["src"]`).

Backends: Xcelium `xrun` and Icarus `iverilog`/`vvp`. Default `--sim auto`
runs EVERY simulator found on PATH (both when both exist — the phase-2 rows
are dual-verified); cases with `"xrun_only": true` skip Icarus (it cannot
parse `case … inside`). With no simulator at all: SKIP, exit 0.

Usage: python3 harness/sv/diff_test2.py [--sim {auto,xrun,iverilog,both}]
                                        [--case NAME] [--workdir DIR] [--keep]
A case with a `"refusal"` field (a refusal kind such as
`"ConversionExpression:signed-constant"`) is a LOUD-REFUSAL row: the model
must REFUSE the design at the case's parameters — the runner exits nonzero —
and the kind must appear in the runner's error or among the envelope's
`Unsupported` kinds. No simulator runs; the row is counted as a refusal,
never as a verified match, and a model that runs is a failure.
Exact documented simulator disagreements are checked against both complete
traces and all bound inputs, and counted separately from verified matches.
Changed or resolved disagreements require review and remain hard failures.
Source-bound tool limitations are reported separately as unavailable coverage.
With a requested simulator available, exit 0 requires no failed cases and at
least one verified case, exact documented disagreement or loud refusal.

THE MULTI-POINT CROSS-CHECK (`--xcheck`, DEFAULT ON; round 3 CX,
`LeanModels/Sv/Probe2.lean`): every row with parameter overrides is also
checked for default-point folds. Per envelope, the extractor re-runs at
every row point of that envelope (`extract.py --probe-points`, into the
work dir — the committed envelope is never touched, and the fresh
default-point envelope must be byte-identical to it, else `XCHECK-STALE`);
the runner then compares the envelope instantiated at the row's point with
slang's own extraction AT that point (`runner2.lean … <probes.json>`).
A difference between two values, a refusal, or slang's metadata/errors at
the point is `XCHECK-FAIL`, a FAILED case, whatever the simulators say. An
`UNCONFIRMED` verdict (the designs are equal except where one side refuses:
slang's tree at the point holds a construct the extractor does not admit)
passes only when every simulator then matches the model at this very point
(`xcheck:UNCONFIRMED, simulator-verified`, counted separately); on a
loud-refusal row the verdict is printed and the row still counts as a
refusal (both outcomes are loud). Envelopes whose sources are not on
this machine report `XCHECK-UNAVAILABLE` (counted, not verified).
`--no-xcheck` turns it off. The extractor runs under `$SV_EXTRACT_PYTHON`
(default: `python3.12` when on PATH, else this interpreter).

XCELIUM IS THE REFERENCE, AS PINNED DATA (`--golden`, DEFAULT OFF): Xcelium is
the reference simulator for ls-sv but is not available everywhere, so its
traces are pinned in `harness/sv/xcelium_golden.json` (captured by
`harness/sv/xcelium_batch.py`, keyed by a content hash of the DUT source, the
testbench, the parameter overrides and the row name; docs/sv-xcelium-reference.md).
With `--golden [PATH]` every simulated row, after its normal checks, is also
compared with its pinned Xcelium trace -- no Xcelium (and, with `--sim` naming
an absent simulator, no simulator at all) is needed -- and reports one of
`XREF-MATCH`, `XREF-DIFF` (the model is suspect), `XREF-STALE` (the sources
changed since the pin: a warning), `XREF-NONE` (no usable pinned trace), plus
totals. `XREF-DIFF` leaves the exit code alone unless `--golden-strict`.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

HARNESS_DIR = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HARNESS_DIR))
CASES_JSON = os.path.join(HARNESS_DIR, "cases2.json")
RUNNER = os.path.join("harness", "sv", "runner2.lean")

sys.path.insert(0, HARNESS_DIR)
import gen_tb2  # noqa: E402
import xcelium_golden  # noqa: E402
from oracle_disagreements import (HarnessError, SimulatorError, oracle_disagreement,
                                 oracle_unavailability, report_annotation)  # noqa: E402

# Dependency order matters: each may import the previous ones.
SV_LEAN_MODULES = ["Basic", "Ast", "Semantics", "Obs", "Sem2", "CombGuard2",
                   "Param", "Param2", "Hier2", "Probe2", "RangeGuard2", "Ingest2"]

SIGMA_NAMES = ("src", "rev")


def run_cmd(cmd, cwd, timeout):
    return subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, universal_newlines=True,
                          timeout=timeout)


def ensure_oleans(verbose):
    libdir = os.path.join(REPO, ".lake", "build", "lib", "lean",
                          "LeanModels", "Sv")
    os.makedirs(libdir, exist_ok=True)
    newest_dep = 0.0
    for name in SV_LEAN_MODULES:
        src = os.path.join(REPO, "LeanModels", "Sv", name + ".lean")
        olean = os.path.join(libdir, name + ".olean")
        newest_dep = max(newest_dep, os.path.getmtime(src))
        if not os.path.exists(olean) or os.path.getmtime(olean) < newest_dep:
            if verbose:
                print("  [olean] rebuilding LeanModels.Sv.%s" % name)
            p = run_cmd(["lake", "env", "lean", "-o", olean, src],
                        cwd=REPO, timeout=900)
            if p.returncode != 0:
                raise HarnessError("lake env lean -o failed for %s:\n%s\n%s"
                                   % (src, p.stdout[-2000:], p.stderr[-2000:]))
        newest_dep = max(newest_dep, os.path.getmtime(olean))


def cycle_lines(text):
    return [ln.rstrip() for ln in text.splitlines() if ln.startswith("CYCLE ")]


def xcheck_lines(text):
    return [ln.rstrip() for ln in text.splitlines() if ln.startswith("XCHECK ")]


def run_lean(envelope, case_name, sigma, probes=None, xout=None):
    """`probes`: a probe sidecar path — the runner then prints the
    case point's `XCHECK` lines first, which are appended to `xout` (a
    list) even when the run itself fails."""
    cmd = ["lake", "env", "lean", "--run", RUNNER, envelope,
           CASES_JSON, case_name, sigma]
    if probes is not None:
        cmd.append(probes)
    p = run_cmd(cmd, cwd=REPO, timeout=900)
    if xout is not None:
        xout.extend(xcheck_lines(p.stdout))
    if p.returncode != 0:
        raise HarnessError("runner2 failed (%d):\n%s\n%s"
                           % (p.returncode, p.stdout[-2000:], p.stderr[-2000:]))
    ports = []
    for ln in p.stdout.splitlines():
        if ln.startswith("PORT "):
            _, name, d, w = ln.split()
            ports.append((name, d, int(w)))
    return ports, cycle_lines(p.stdout)


def extractor_python():
    env = os.environ.get("SV_EXTRACT_PYTHON")
    if env:
        return env
    return shutil.which("python3.12") or sys.executable


def case_point(case):
    """The row's parameter overrides as `[(name, int)]`, or None when the
    row has none (or a non-integer one: the runner skips those too)."""
    params = case.get("params") or {}
    pt = []
    for k, v in sorted(params.items()):
        if isinstance(v, bool) or not isinstance(v, int):
            return None
        pt.append((k, v))
    return pt or None


def prepare_probes(cases, base, verbose):
    """Re-extract every envelope that a row with overrides uses, at all
    of its rows' points, into `base/xcheck/`. Returns `{envelope: (status,
    sidecar or detail)}` with status `ok` / `stale` / `unavailable` /
    `error`."""
    groups = {}
    for case in cases:
        pt = case_point(case)
        if pt is None:
            continue
        fbase = case.get("file", case["top"])
        envelope = os.path.join(REPO, "Examples", "system-verilog",
                                case["example"], fbase + ".sv.json")
        pts = groups.setdefault(envelope, [])
        if pt not in pts:
            pts.append(pt)
    outdir = os.path.join(base, "xcheck")
    os.makedirs(outdir, exist_ok=True)
    result = {}
    for envelope, pts in groups.items():
        try:
            with open(envelope) as f:
                env = json.load(f)
            srcs = [s if isinstance(s, str) else s["path"] for s in env["source_files"]]
            if not all(os.path.exists(os.path.join(REPO, s)) for s in srcs):
                result[envelope] = ("unavailable", "sources not on this machine")
                continue
            out = os.path.join(outdir, os.path.relpath(envelope, REPO).replace(os.sep, "__"))
            spec = ";".join(",".join("%s=%d" % kv for kv in pt) for pt in pts)
            p = run_cmd([extractor_python(), os.path.join("extractors", "sv", "extract.py"),
                         "--top", env["top"], *srcs, "-o", out, "--probe-points", spec],
                        cwd=REPO, timeout=900)
            if p.returncode != 0:
                result[envelope] = ("error", "extractor failed (%d): %s"
                                    % (p.returncode, p.stderr[-1500:]))
                continue
            with open(out, "rb") as f1, open(envelope, "rb") as f2:
                if f1.read() != f2.read():
                    result[envelope] = ("stale", "a fresh extraction of the envelope differs "
                                        "from the committed one (regenerate it)")
                    continue
            result[envelope] = ("ok", out[:-5] + ".probes.json")
            if verbose:
                print("  [xcheck] %s: %d point(s)" % (os.path.relpath(envelope, REPO), len(pts)))
        except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as exc:
            result[envelope] = ("error", "probe extraction failed: %s" % exc)
    return result


def run_xcelium(dut_sv, tb_text, workdir):
    os.makedirs(workdir, exist_ok=True)
    tb_path = os.path.join(workdir, "tb.sv")
    with open(tb_path, "w") as f:
        f.write(tb_text)
    p = run_cmd(["xrun", "-sv", "-q", "-timescale", "1ns/1ns", dut_sv, tb_path],
                cwd=workdir, timeout=900)
    if p.returncode != 0:
        raise HarnessError("xrun failed (%d) in %s:\n%s\n%s"
                           % (p.returncode, workdir, p.stdout[-3000:],
                              p.stderr[-2000:]))
    return cycle_lines(p.stdout)


def run_iverilog(dut_sv, tb_text, workdir):
    os.makedirs(workdir, exist_ok=True)
    tb_path = os.path.join(workdir, "tb.sv")
    with open(tb_path, "w") as f:
        f.write(tb_text)
    sim_path = os.path.join(workdir, "sim")
    p = run_cmd(["iverilog", "-g2012", "-o", sim_path, tb_path, dut_sv],
                cwd=workdir, timeout=300)
    if p.returncode != 0:
        raise SimulatorError("iverilog failed (%d) in %s:\n%s\n%s"
                           % (p.returncode, workdir, p.stdout[-3000:],
                              p.stderr[-2000:]), "compile", p)
    p = run_cmd(["vvp", sim_path], cwd=workdir, timeout=900)
    if p.returncode != 0:
        raise SimulatorError("vvp failed (%d) in %s:\n%s\n%s"
                           % (p.returncode, workdir, p.stdout[-3000:],
                              p.stderr[-2000:]), "runtime", p)
    return cycle_lines(p.stdout)


def envelope_refusal_kinds(envelope):
    """Every `Unsupported` kind of an envelope (the extractor's refusals)."""
    found = set()

    def walk(node):
        if isinstance(node, dict):
            if node.get("kind") == "Unsupported" and isinstance(node.get("sv_kind"), str):
                found.add(node["sv_kind"])
            for value in node.values():
                walk(value)
        elif isinstance(node, list):
            for value in node:
                walk(value)

    with open(envelope) as handle:
        walk(json.load(handle))
    return found


def check_refusal(case, envelope, sigma, probes=None, xout=None):
    """A loud-refusal row: `(True, detail)` when the runner refuses the
    case and names the expected kind (in its error or the envelope)."""
    kind = case["refusal"]
    try:
        run_lean(envelope, case["name"], sigma, probes, xout)
    except HarnessError as exc:
        if kind in str(exc) or kind in envelope_refusal_kinds(envelope):
            return True, kind
        return False, "refused, but not for %s:\n%s" % (kind, exc)
    return False, "expected a loud refusal (%s); the model ran" % kind


def diff_traces(sim_lines, lean_lines):
    if sim_lines == lean_lines:
        return None
    msgs = []
    for i in range(max(len(sim_lines), len(lean_lines))):
        s = sim_lines[i] if i < len(sim_lines) else "<missing>"
        l = lean_lines[i] if i < len(lean_lines) else "<missing>"
        if s != l:
            msgs.append("  sim : %s\n  lean: %s" % (s, l))
            if len(msgs) >= 3:
                break
    return "\n".join(msgs)


def requested_simulators(requested):
    have_xrun = shutil.which("xrun") is not None
    have_iv = (shutil.which("iverilog") is not None
               and shutil.which("vvp") is not None)
    if requested == "xrun":
        return ["xrun"] if have_xrun else []
    if requested == "iverilog":
        return ["iverilog"] if have_iv else []
    return [name for name, available in (("xrun", have_xrun), ("iverilog", have_iv))
            if available]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sim", choices=["auto", "xrun", "iverilog", "both"],
                    default="auto")
    ap.add_argument("--case", default=None)
    ap.add_argument("--workdir", default=None)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--xcheck", action=argparse.BooleanOptionalAction, default=True,
                    help="multi-point cross-check of every row with parameter "
                    "overrides (default: on)")
    ap.add_argument("--golden", nargs="?", const=xcelium_golden.GOLDEN_JSON, default=None,
                    metavar="PATH", help="also compare each simulated row with its pinned "
                    "Xcelium trace (default file: harness/sv/xcelium_golden.json; default: off)")
    ap.add_argument("--golden-strict", action="store_true",
                    help="with --golden: XREF-DIFF rows make the exit code nonzero")
    args = ap.parse_args()

    with open(CASES_JSON) as f:
        spec = json.load(f)
    cases = spec["cases"]
    if args.case is not None:
        cases = [c for c in cases if c["name"] == args.case]
        if not cases:
            print("no case named %r" % args.case)
            return 2

    # OPS-148 shape (d): this printed "all 0 case(s) passed" and exited 0.
    if not cases:
        print("diff_test2: COULD NOT VERIFY -- the case file has NO cases (%s)"
              % CASES_JSON)
        print("Nothing was compared, so this is not a pass.")
        return 1

    xref = None
    if args.golden is not None:
        try:
            xref = xcelium_golden.Xref(args.golden)
        except (OSError, ValueError) as exc:
            print("diff_test2: --golden: %s" % exc)
            return 2

    sims = requested_simulators(args.sim)
    if not sims and xref is None:
        print("SKIP: no requested simulator on PATH (sv phase-2 differential "
              "harness not exercised)")
        return 0

    ensure_oleans(args.verbose)

    base = args.workdir or tempfile.mkdtemp(prefix="sv2diff_")
    failures = 0
    verified = 0
    skipped = 0
    disagreements = 0
    unavailable_backends = 0
    refusals = 0
    xchecked = 0
    xunconfirmed = 0
    xunavailable = 0
    probes = prepare_probes(cases, base, args.verbose) if args.xcheck else {}
    for case in cases:
        name = case["name"]
        example = case["example"]
        top = case["top"]
        # Source file base name; defaults to the top module's name (the
        # register_file lives in cv32e40p_register_file_ff.sv but declares
        # module cv32e40p_register_file).
        fbase = case.get("file", top)
        dut_sv = os.path.join(REPO, "Examples", "system-verilog", example,
                              fbase + ".sv")
        envelope = dut_sv + ".json"
        sigmas = case.get("accept_sigmas", ["src"])
        case_sims = [s for s in sims
                     if not (case.get("xrun_only") and s == "iverilog")]
        if not case_sims and xref is None:
            skipped += 1
            print("%-24s SKIP (needs xrun; not selected or unavailable)" % name)
            continue
        # The multi-point cross-check of this row (round 3 CX).
        xprobe = None
        xstatus = None
        if args.xcheck and case_point(case) is not None:
            st, info = probes.get(envelope, ("error", "no probe extraction"))
            if st == "ok":
                xprobe = info
            else:
                xstatus = (st, info)
        xout = []
        if "refusal" in case:
            ok, detail = check_refusal(case, envelope, sigmas[0], xprobe, xout)
            xnote = ""
            if xprobe is not None:
                bad = [ln for ln in xout if not ln.startswith("XCHECK ok")]
                xnote = "; xcheck: %s" % ("agree" if xout and not bad else
                                          "not agree (a loud row: informational): "
                                          + " | ".join(ln[:200] for ln in bad or ["no XCHECK line"]))
            elif xstatus is not None:
                xnote = "; xcheck %s" % xstatus[0]
            if ok:
                refusals += 1
                print("%-24s REFUSED (loud: %s; not a match%s)" % (name, detail, xnote))
            else:
                failures += 1
                print("%-24s FAIL: %s" % (name, detail))
                report_annotation("%s: %s" % (name, detail), level="error",
                                  title="SV differential failure")
            continue
        if xstatus is not None:
            if xstatus[0] == "unavailable":
                xunavailable += 1
                print("%-24s XCHECK-UNAVAILABLE: %s (cross-check not run)" % (name, xstatus[1]))
            else:
                failures += 1
                print("%-24s XCHECK-%s: %s" % (name, xstatus[0].upper(), xstatus[1]))
                report_annotation("%s: cross-check %s: %s" % (name, xstatus[0], xstatus[1]),
                                  level="error", title="SV differential failure")
                continue
        try:
            lean = {}
            ports = None
            for i, sg in enumerate(sigmas):
                ports, lines = run_lean(envelope, name, sg,
                                        xprobe if i == 0 else None, xout)
                lean[sg] = lines
            # The cross-check verdict: `FAIL` lines (a silent difference, a
            # refusal, slang's metadata or errors at the point) fail the
            # case outright; `UNCONFIRMED` lines (the designs are equal
            # except where one side refuses) fail it unless the simulators
            # then verify the model at this very point (decided below).
            xunconf = []
            if xprobe is not None:
                xfail = [ln for ln in xout if not ln.startswith(("XCHECK ok", "XCHECK UNCONFIRMED"))]
                xunconf = [ln for ln in xout if ln.startswith("XCHECK UNCONFIRMED")]
                if not xout or xfail:
                    failures += 1
                    # The verdict line says what failed: only a `differ`
                    # verdict is a default-point fold.
                    print("%-24s XCHECK-FAIL: the multi-point cross-check does not agree at this point" % name)
                    for ln in xfail or ["(no XCHECK line)"]:
                        print("  " + ln)
                    report_annotation("%s: XCHECK-FAIL\n%s" % (name, "\n".join(xfail)),
                                      level="error", title="SV differential failure")
                    continue
            results = []
            ok = True
            declared_case = False
            compared = False
            unavailable_case = False
            for sim in case_sims:
                wd = os.path.join(base, name, sim)
                tb = gen_tb2.generate_tb2(top, ports, case)
                try:
                    sim_lines = (run_xcelium if sim == "xrun" else run_iverilog)(
                        dut_sv, tb, wd)
                except SimulatorError as error:
                    if sim != "iverilog":
                        raise
                    with open(dut_sv, "rb") as handle:
                        source_bytes = handle.read()
                    with open(envelope, "rb") as handle:
                        envelope_bytes = handle.read()
                    unavailable = oracle_unavailability(
                        case, source_bytes, envelope_bytes, tb, dut_sv, error)
                    if unavailable is None:
                        raise
                    unavailable_case = True
                    unavailable_backends += 1
                    results.append("iverilog:UNAVAILABLE (%s)" % unavailable)
                    print("%-24s UNAVAILABLE ORACLE: %s (not verified)" % (name, unavailable))
                    print(error)
                    report_annotation("%s: unavailable Icarus oracle %s; not verified" % (name, unavailable))
                    continue
                if sim == "iverilog" and "icarus_unavailable" in case:
                    raise HarnessError("%s: Icarus restriction resolved; retire the declaration" % name)
                declared = None
                if "oracle_disagreement" in case:
                    with open(dut_sv, "rb") as handle:
                        source_bytes = handle.read()
                    with open(envelope, "rb") as handle:
                        envelope_bytes = handle.read()
                    declared = oracle_disagreement(
                        case, sim, source_bytes, envelope_bytes, tb, sim_lines, lean)
                if declared:
                    declared_case = True
                    results.append("%s:DECLARED DISAGREEMENT (%s)" % (sim, declared))
                    print("%-24s DECLARED SIMULATOR DISAGREEMENT: %s (not a match)"
                          % (name, declared))
                    print("  Reference: %s" % case["oracle_disagreement"]["reference"])
                    for label, trace in (("sim", sim_lines), ("lean", lean[sigmas[0]])):
                        for line in trace:
                            print("  %s: %s" % (label, line))
                    report_annotation("%s: declared simulator disagreement %s; not a match" % (name, declared))
                    continue
                compared = True
                matched = None
                for sg in sigmas:
                    if sim_lines == lean[sg]:
                        matched = sg
                        break
                if matched is None:
                    ok = False
                    results.append("%s:MISMATCH" % sim)
                    print("%-24s FAIL vs %s" % (name, sim))
                    difference = diff_traces(sim_lines, lean[sigmas[0]])
                    print(difference)
                    report_annotation("%s: mismatch vs %s\n%s" % (name, sim, difference),
                                      level="error", title="SV differential failure")
                else:
                    results.append("%s:ok(%s)" % (sim, matched))
            if ok and xunconf and (declared_case or unavailable_case or not compared):
                # Nothing but a simulator at this point could vouch for the
                # envelope where the point extraction refuses: unverified.
                ok = False
                print("%-24s XCHECK-FAIL: cross-check UNCONFIRMED and no simulator verified the point" % name)
                for ln in xunconf:
                    print("  " + ln)
            if ok:
                if xprobe is not None:
                    if xunconf:
                        xunconfirmed += 1
                        results.append("xcheck:UNCONFIRMED, simulator-verified")
                        for ln in xunconf:
                            print("  " + ln)
                    else:
                        xchecked += 1
                        results.append("xcheck:agree")
                if declared_case:
                    disagreements += 1
                elif compared:
                    verified += 1
                else:
                    skipped += 1
                print("%-24s %s  [%s]  (%d cycles)"
                      % (name, "SKIP" if not compared and not declared_case else
                         "CHECKED" if declared_case or unavailable_case else "PASS",
                         ", ".join(results), len(lean[sigmas[0]])))
            else:
                failures += 1
            if xref is not None:
                status, detail = xref.check(
                    name, dut_sv, gen_tb2.generate_tb2(top, ports, case),
                    case.get("params"), [lean[sg] for sg in sigmas], diff_traces)
                print("%-24s %s" % (name, status))
                for ln in detail:
                    print("  " + ln)
        except (HarnessError, gen_tb2.TbError) as exc:
            failures += 1
            print("%-24s ERROR: %s" % (name, exc))
            report_annotation("%s: %s" % (name, exc), level="error",
                              title="SV differential failure")
    if not args.keep and args.workdir is None:
        shutil.rmtree(base, ignore_errors=True)
    if xref is not None:
        print(xref.summary())
    if failures:
        print("%d case(s) failed" % failures)
        return 1
    print("%d case(s) verified, %d skipped, %d declared simulator disagreement(s), %d unavailable backend(s), %d loud refusal(s)"
          % (verified, skipped, disagreements, unavailable_backends, refusals))
    if args.xcheck:
        print("multi-point cross-check: %d row point(s) agree, %d unconfirmed but "
              "simulator-verified, %d unavailable (sources off-machine)"
              % (xchecked, xunconfirmed, xunavailable))
    if xref is not None and args.golden_strict and xref.counts["diff"]:
        print("--golden-strict: %d XREF-DIFF row(s)" % xref.counts["diff"])
        return 1
    return 0 if (verified or disagreements or refusals
                 or (xref is not None and xref.counts["match"] + xref.counts["diff"])) else 1


if __name__ == "__main__":
    sys.exit(main())
