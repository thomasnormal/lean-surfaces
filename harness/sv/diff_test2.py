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
Exact documented simulator disagreements are checked against both complete
traces and all bound inputs, and counted separately from verified matches.
Changed or resolved disagreements require review and remain hard failures.
Source-bound tool limitations are reported separately as unavailable coverage.
With a requested simulator available, exit 0 requires no failed cases and at
least one verified case or exact documented disagreement.
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
from oracle_disagreements import (HarnessError, SimulatorError, oracle_disagreement,
                                 oracle_unavailability, report_annotation)  # noqa: E402

# Dependency order matters: each may import the previous ones.
SV_LEAN_MODULES = ["Basic", "Ast", "Semantics", "Obs", "Sem2", "Param",
                   "Param2", "Ingest2"]

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


def run_lean(envelope, case_name, sigma):
    p = run_cmd(["lake", "env", "lean", "--run", RUNNER, envelope,
                 CASES_JSON, case_name, sigma], cwd=REPO, timeout=900)
    if p.returncode != 0:
        raise HarnessError("runner2 failed (%d):\n%s\n%s"
                           % (p.returncode, p.stdout[-2000:], p.stderr[-2000:]))
    ports = []
    for ln in p.stdout.splitlines():
        if ln.startswith("PORT "):
            _, name, d, w = ln.split()
            ports.append((name, d, int(w)))
    return ports, cycle_lines(p.stdout)


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

    sims = requested_simulators(args.sim)
    if not sims:
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
        if not case_sims:
            skipped += 1
            print("%-24s SKIP (needs xrun; not selected or unavailable)" % name)
            continue
        try:
            lean = {}
            ports = None
            for sg in sigmas:
                ports, lines = run_lean(envelope, name, sg)
                lean[sg] = lines
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
                    print(diff_traces(sim_lines, lean[sigmas[0]]))
                else:
                    results.append("%s:ok(%s)" % (sim, matched))
            if ok:
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
        except (HarnessError, gen_tb2.TbError) as exc:
            failures += 1
            print("%-24s ERROR: %s" % (name, exc))
    if not args.keep and args.workdir is None:
        shutil.rmtree(base, ignore_errors=True)
    if failures:
        print("%d case(s) failed" % failures)
        return 1
    print("%d case(s) verified, %d skipped, %d declared simulator disagreement(s), %d unavailable backend(s)"
          % (verified, skipped, disagreements, unavailable_backends))
    return 0 if verified or disagreements else 1


if __name__ == "__main__":
    sys.exit(main())
