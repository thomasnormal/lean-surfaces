#!/usr/bin/env python3
"""SV M0 differential harness: Lean cycle semantics vs a reference simulator.

Backends (--sim): Xcelium `xrun` (normative for M0, present on the lab host)
and Icarus Verilog `iverilog`/`vvp` (portable, used on generic CI; 4-state,
so x/z cases are in scope). Default `auto` prefers xrun, falls back to
iverilog, and — so CI step logic stays simple — prints a SKIP line and exits
0 when NO simulator is on PATH. When a simulator exists, any mismatch is a
hard failure.

Per case in harness/sv/cases.json:
  1. generate a testbench (gen_tb.py) from the case + the example's extractor
     envelope (Examples/<name>/<name>.sv.json), run it under the selected
     simulator in a /tmp work dir, and collect the canonical
     `CYCLE <k> <name>=<binary>...` lines (negedge-sampled);
  2. run the Lean interpreter on the same envelope + case via
     `lake env lean --run harness/sv/runner.lean` and collect its lines;
  3. diff line-by-line. A case passes iff the simulator trace equals the Lean
     trace for some schedule in the case's `accept_sigmas` (default: just
     `src`, source order; `race_blk` legitimately accepts `src` or `rev` and
     the table reports which one matched).

Any mismatch is an interpreter bug (the simulator is normative for M0).

Usage: python3 harness/sv/diff_test.py [--sim {auto,xrun,iverilog}]
                                       [--case NAME] [--workdir DIR] [--keep]
Exit status: 0 iff every selected case passed (or no simulator exists in
--sim auto, reported as SKIP).

Prerequisite plumbing: the runner imports LeanModels.Sv.*, whose oleans are
NOT built by plain `lake build` (the SV lane is invisible to it in M0), so
this script first (re)builds any stale Sv olean into .lake/build/lib/lean
with `lake env lean -o` — the same emission discipline the SV Lean files
themselves use. It never runs plain `lake build`.
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
CASES_JSON = os.path.join(HARNESS_DIR, "cases.json")
RUNNER = os.path.join("harness", "sv", "runner.lean")  # repo-relative for lake

sys.path.insert(0, HARNESS_DIR)
import gen_tb  # noqa: E402

# Dependency order matters: each may import the previous ones.
SV_LEAN_MODULES = ["Basic", "Ast", "Json", "Semantics"]

SIGMA_NAMES = ("src", "rev")


class HarnessError(Exception):
    pass


def run_cmd(cmd, cwd, timeout):
    p = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, universal_newlines=True,
                       timeout=timeout)
    return p


def ensure_oleans(verbose):
    """(Re)build any missing/stale LeanModels.Sv olean the runner imports."""
    libdir = os.path.join(REPO, ".lake", "build", "lib", "lean", "LeanModels", "Sv")
    os.makedirs(libdir, exist_ok=True)
    newest_dep = 0.0
    for name in SV_LEAN_MODULES:
        src = os.path.join(REPO, "LeanModels", "Sv", name + ".lean")
        olean = os.path.join(libdir, name + ".olean")
        newest_dep = max(newest_dep, os.path.getmtime(src))
        if not os.path.exists(olean) or os.path.getmtime(olean) < newest_dep:
            if verbose:
                print("  [olean] rebuilding LeanModels.Sv.%s" % name)
            p = run_cmd(["lake", "env", "lean", "-o", olean, src], cwd=REPO, timeout=600)
            if p.returncode != 0:
                raise HarnessError("lake env lean -o failed for %s:\n%s\n%s"
                                   % (src, p.stdout[-2000:], p.stderr[-2000:]))
        newest_dep = max(newest_dep, os.path.getmtime(olean))


def cycle_lines(text):
    return [ln.rstrip() for ln in text.splitlines() if ln.startswith("CYCLE ")]


def run_xcelium(example_sv, tb_text, workdir):
    os.makedirs(workdir, exist_ok=True)
    tb_path = os.path.join(workdir, "tb.sv")
    with open(tb_path, "w") as f:
        f.write(tb_text)
    cmd = ["xrun", "-sv", "-q", "-timescale", "1ns/1ns", example_sv, tb_path]
    p = run_cmd(cmd, cwd=workdir, timeout=600)
    if p.returncode != 0:
        raise HarnessError("xrun failed (%d) in %s:\n%s\n%s"
                           % (p.returncode, workdir, p.stdout[-3000:], p.stderr[-2000:]))
    return cycle_lines(p.stdout)


def run_iverilog(example_sv, tb_text, workdir):
    os.makedirs(workdir, exist_ok=True)
    tb_path = os.path.join(workdir, "tb.sv")
    with open(tb_path, "w") as f:
        f.write(tb_text)
    sim_path = os.path.join(workdir, "sim")
    p = run_cmd(["iverilog", "-g2012", "-o", sim_path, tb_path, example_sv],
                cwd=workdir, timeout=300)
    if p.returncode != 0:
        raise HarnessError("iverilog failed (%d) in %s:\n%s\n%s"
                           % (p.returncode, workdir, p.stdout[-3000:], p.stderr[-2000:]))
    p = run_cmd(["vvp", sim_path], cwd=workdir, timeout=600)
    if p.returncode != 0:
        raise HarnessError("vvp failed (%d) in %s:\n%s\n%s"
                           % (p.returncode, workdir, p.stdout[-3000:], p.stderr[-2000:]))
    return cycle_lines(p.stdout)


# name -> (runner, tools that must be on PATH)
SIMULATORS = {
    "xrun": (run_xcelium, ("xrun",)),
    "iverilog": (run_iverilog, ("iverilog", "vvp")),
}


def sim_available(name):
    return all(shutil.which(t) for t in SIMULATORS[name][1])


def resolve_sim(requested):
    """Return the simulator name to use, or None for a --sim auto SKIP."""
    if requested != "auto":
        if not sim_available(requested):
            missing = [t for t in SIMULATORS[requested][1] if not shutil.which(t)]
            raise HarnessError("--sim %s requested but not on PATH (missing: %s)"
                               % (requested, ", ".join(missing)))
        return requested
    for name in ("xrun", "iverilog"):  # xrun (normative) preferred
        if sim_available(name):
            return name
    return None


def run_lean(envelope_rel, case_name, sigma):
    cmd = ["lake", "env", "lean", "--run", RUNNER,
           envelope_rel, os.path.join("harness", "sv", "cases.json"),
           case_name, sigma]
    p = run_cmd(cmd, cwd=REPO, timeout=600)
    if p.returncode != 0:
        raise HarnessError("lean runner failed (%d) for %s [%s]:\n%s\n%s"
                           % (p.returncode, case_name, sigma,
                              p.stdout[-2000:], p.stderr[-2000:]))
    return cycle_lines(p.stdout)


def show_diff(sim, case_name, sigma, sim_lines, lean):
    print("  MISMATCH for case '%s' (sigma=%s): %s (ground truth) vs Lean:"
          % (case_name, sigma, sim))
    n = max(len(sim_lines), len(lean))
    for i in range(n):
        x = sim_lines[i] if i < len(sim_lines) else "<missing>"
        l = lean[i] if i < len(lean) else "<missing>"
        marker = " " if x == l else "!"
        print("  %s %8s: %s" % (marker, sim, x))
        if x != l:
            print("  %s     lean: %s" % (marker, l))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--sim", choices=["auto", "xrun", "iverilog"], default="auto",
                    help="simulator backend (auto: xrun if on PATH, else "
                         "iverilog, else SKIP with exit 0)")
    ap.add_argument("--case", help="run only the named case")
    ap.add_argument("--workdir", help="simulator work dir (default: mkdtemp under /tmp)")
    ap.add_argument("--keep", action="store_true", help="keep the work dir")
    args = ap.parse_args()

    sim = resolve_sim(args.sim)
    if sim is None:
        print("SKIP: no simulator on PATH (want xrun or iverilog+vvp) -- "
              "nothing verified, exiting 0")
        return 0
    run_sim = SIMULATORS[sim][0]
    print("simulator: %s" % sim)

    with open(CASES_JSON) as f:
        cases_doc = json.load(f)
    cases = cases_doc["cases"]
    if args.case:
        cases = [c for c in cases if c["name"] == args.case]
        if not cases:
            print("no case named '%s'" % args.case)
            return 2

    workroot = args.workdir or tempfile.mkdtemp(prefix="sv-diff-", dir="/tmp")
    made_tmp = args.workdir is None
    print("workdir: %s" % workroot)

    print("ensuring LeanModels.Sv oleans are fresh ...")
    ensure_oleans(verbose=True)

    results = []
    all_pass = True
    for case in cases:
        name = case["name"]
        example = case["example"]
        sigmas = case.get("accept_sigmas", ["src"])
        for s in sigmas:
            if s not in SIGMA_NAMES:
                raise HarnessError("case %s: unknown sigma '%s'" % (name, s))
        envelope_rel = os.path.join("Examples", example, example + ".sv.json")
        example_sv = os.path.join(REPO, "Examples", example, example + ".sv")
        with open(os.path.join(REPO, envelope_rel)) as f:
            envelope = json.load(f)

        print("case %-20s (%s, %d cycles) ..." % (name, example, len(case["stimulus"])))
        tb_text = gen_tb.generate_tb(envelope, case)
        sim_trace = run_sim(example_sv, tb_text, os.path.join(workroot, name))
        if len(sim_trace) != len(case["stimulus"]):
            raise HarnessError("case %s: %s produced %d CYCLE lines for %d cycles"
                               % (name, sim, len(sim_trace), len(case["stimulus"])))

        matched = None
        lean_by_sigma = {}
        for sigma in sigmas:
            lean = run_lean(envelope_rel, name, sigma)
            lean_by_sigma[sigma] = lean
            if lean == sim_trace:
                matched = sigma
                break
        if matched is None:
            all_pass = False
            for sigma in sigmas:
                show_diff(sim, name, sigma, sim_trace, lean_by_sigma[sigma])
        results.append((name, example, len(case["stimulus"]), sigmas, matched))

    print()
    print("simulator: %s" % sim)
    print("%-22s %-10s %7s  %-18s %s" % ("CASE", "EXAMPLE", "CYCLES", "SIGMA", "RESULT"))
    print("-" * 72)
    for name, example, ncyc, sigmas, matched in results:
        if matched is None:
            sig = "/".join(sigmas)
            res = "FAIL"
        else:
            sig = "sigma_" + matched
            res = "PASS" if sigmas == ["src"] else "PASS (matched %s)" % ("sigma_" + matched)
        print("%-22s %-10s %7d  %-18s %s" % (name, example, ncyc, sig, res))
    print("-" * 72)
    print("overall: %s" % ("PASS" if all_pass else "FAIL"))

    if made_tmp and not args.keep and all_pass:
        shutil.rmtree(workroot, ignore_errors=True)
    return 0 if all_pass else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except HarnessError as e:
        print("HARNESS ERROR: %s" % e)
        sys.exit(3)
