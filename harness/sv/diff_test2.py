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
Exit 0 iff every selected case passed on every exercised simulator.
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

# Dependency order matters: each may import the previous ones.
SV_LEAN_MODULES = ["Basic", "Ast", "Semantics", "Obs", "Sem2", "Param",
                   "Param2", "Ingest2"]

SIGMA_NAMES = ("src", "rev")


class HarnessError(Exception):
    pass


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
        raise HarnessError("iverilog failed (%d) in %s:\n%s\n%s"
                           % (p.returncode, workdir, p.stdout[-3000:],
                              p.stderr[-2000:]))
    p = run_cmd(["vvp", sim_path], cwd=workdir, timeout=900)
    if p.returncode != 0:
        raise HarnessError("vvp failed (%d) in %s:\n%s\n%s"
                           % (p.returncode, workdir, p.stdout[-3000:],
                              p.stderr[-2000:]))
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sim", choices=["auto", "xrun", "iverilog", "both"],
                    default="auto")
    ap.add_argument("--case", default=None)
    ap.add_argument("--workdir", default=None)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    have_xrun = shutil.which("xrun") is not None
    have_iv = (shutil.which("iverilog") is not None
               and shutil.which("vvp") is not None)
    if args.sim == "xrun":
        sims = ["xrun"] if have_xrun else []
    elif args.sim == "iverilog":
        sims = ["iverilog"] if have_iv else []
    else:  # auto/both: everything available (dual verification)
        sims = [s for s, ok in (("xrun", have_xrun), ("iverilog", have_iv)) if ok]
    if not sims:
        print("SKIP: no requested simulator on PATH (sv phase-2 differential "
              "harness not exercised)")
        return 0

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

    ensure_oleans(args.verbose)

    base = args.workdir or tempfile.mkdtemp(prefix="sv2diff_")
    failures = 0
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
            print("%-24s SKIP (needs xrun; not on PATH)" % name)
            continue
        try:
            lean = {}
            ports = None
            for sg in sigmas:
                ports, lines = run_lean(envelope, name, sg)
                lean[sg] = lines
            results = []
            ok = True
            for sim in case_sims:
                wd = os.path.join(base, name, sim)
                tb = gen_tb2.generate_tb2(top, ports, case)
                sim_lines = (run_xcelium if sim == "xrun" else run_iverilog)(
                    dut_sv, tb, wd)
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
                print("%-24s PASS  [%s]  (%d cycles)"
                      % (name, ", ".join(results), len(lean[sigmas[0]])))
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
    print("all %d case(s) passed" % len(cases))
    return 0


if __name__ == "__main__":
    sys.exit(main())
