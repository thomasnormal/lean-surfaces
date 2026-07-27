#!/usr/bin/env python3
"""Differential measurement harness for the amplifier demo decks.

Rung 1 of the amp campaign's measurement ladder (docs/amp-demo.md): every
prediction the Lean proofs make about `cs_amp.cir` and `diff_pair.cir` is
checked against a simulator before anyone solders anything.

* `.op` rows wrap the testbench-free component decks with ideal supply and
  input sources and compare simulated node voltages and the supply branch
  current against the EXACT rational operating points proved in Lean
  (Examples/spice/cs_amp/proof.lean: cs_amp_op / cs_amp_transfer /
  cs_amp_cutoff; Examples/spice/diff_pair/proof.lean: diff_pair_balanced /
  diff_pair_cmrr / diff_pair_probe). The expected values in amp_cases.json
  are additionally recomputed here from the deck constants, so a drifted
  deck, a drifted case table, or a drifted simulator all fail the harness.
* The GAIN sweep row runs a `.dc` sweep across the proved tolerance-box
  window (39/20, 41/20), finite-differences the measured transfer curve at
  the 2 V bias, and asserts the measured gain lands INSIDE the proved
  closed interval [-726/125, -486/125] (cs_amp_gain_interval) AND within
  model-accuracy tolerance of the nominal -beta*Vov*RD = -24/5
  (cs_amp_gain_deriv). The interval endpoints are recomputed here from the
  deck constants and the +-10% box, and must agree with the case table.
* The CLIPPING sweep row drives the input from ground into the low rail
  and asserts the proved three-region structure (cs_amp_regions):
  cutoff plateau at VDD, strict monotone fall past threshold, and the
  low-rail approach, with every sweep point checked against the proved
  region-wise transfer (the triode branch against the closed-form
  quadratic root of the same MOS1 physics; vin = 7/2 against the exact
  rational 5/12 of cs_amp_triode_point).
* The DIFFERENTIAL sweep row sweeps the differential drive d across the
  proved window |d| <= 1/2, checks the measured vod against the proved
  large-signal transfer -4*d*sqrt(1 - d^2/4) (diff_pair_vod) point by
  point plus its odd symmetry, and finite-differences the balance gain
  against the PROVED derivative -4 (diff_pair_gain); the O(h^2)
  central-difference bias of the proved curve, -4*sqrt(1 - h^2/4), is
  itself predicted in closed form and checked.
* The COMMON-MODE sweep rows sweep the common mode at fixed differential
  drive (d = 0 over the balanced window cm <= 4, and d = 1/2 over the
  proved CMRR window cm <= 21/8) and assert near-invariance of both
  outputs in floating point — the proof (diff_pair_cmrr) says EXACT
  invariance at the ideal model (LAMBDA = 0, ideal tail) — plus the tail
  node tracking cm - VTO - u.

The cs_amp triode `.op` row has no exact rational operating point (its
load-line quadratic has an irrational discriminant; by design the Lean
window stops at vin = 9/4); it is checked in floating point against the
closed-form quadratic root of the same MOS1 physics.

`--sim spectre` runs the same case table against Cadence Spectre as an
independent second oracle (spice-compatibility mode, nutascii raw output;
supply branch current probed as `vdd:p` instead of `vdd#branch`). Both
simulators are untrusted differential oracles: the Lean theorems do not
depend on these floating-point comparisons, and agreement does not by
itself establish physical model validity (see the evidence layer in
LeanModels/Spice/CommonSource.lean and docs/amp-demo.md).
"""

import argparse
import json
import math
import os
import re
import shutil
import subprocess
import tempfile
from fractions import Fraction
from pathlib import Path

import spectre_test  # parse_nutascii: the Spectre raw-file reader

ROOT = Path(__file__).resolve().parents[2]
CASES = Path(__file__).with_name("amp_cases.json")

# Deck constants of Examples/spice/cs_amp/cs_amp.cir, fixed by the checked
# adapter theorem `cs_amp_topology` (VTO=1, KP=400u -> beta=1/2500, RD=12k).
CS_AMP_VTO = Fraction(1)
CS_AMP_BETA = Fraction(1, 2500)
CS_AMP_RD = Fraction(12000)
# The proved tolerance box of cs_amp_gain_interval: VTO and beta both +-10%.
CS_AMP_BOX = Fraction(1, 10)

# Deck constants of Examples/spice/diff_pair/diff_pair.cir, fixed by the
# checked adapter theorem `diff_pair_topology` (VTO=1, KP=400u ->
# beta=1/2500, RD=10k, I_TAIL=400u). I_TAIL/beta = 1 V^2 BY DESIGN, so the
# balanced overdrive is exactly 1 V and the balance gain is exactly -4.
DP_VTO = Fraction(1)
DP_BETA = Fraction(1, 2500)
DP_RD = Fraction(10000)
DP_ITAIL = Fraction(1, 2500)

TIGHT_OPTIONS = ".options reltol=1e-9 abstol=1e-15 vntol=1e-12"


def ngspice_path():
    found = shutil.which("ngspice")
    if found:
        return found
    local = Path.home() / ".local/bin/ngspice"
    if local.exists():
        return str(local)
    raise SystemExit("ngspice not found on PATH or at ~/.local/bin/ngspice")


def spectre_path():
    found = shutil.which("spectre")
    if found:
        return found
    candidate = os.environ.get(
        "SPECTRE_BIN", "/opt/cadence/installs/SPECTRE231/bin/spectre")
    if Path(candidate).exists():
        return candidate
    raise SystemExit("spectre not found on PATH (set SPECTRE_BIN)")


def predicted_op(supply, vin):
    """Exact operating point of the resistor-loaded common-source stage.

    Mirrors the proved region analysis: cutoff (cs_amp_cutoff), the
    saturation window (cs_amp_op / cs_amp_transfer / cs_amp_saturation),
    and the triode fallback beyond the window. Returns (region, out,
    supply_current) where out/current are Fraction for the proved regions
    and float for triode.
    """
    vov = vin - CS_AMP_VTO
    if vov <= 0:
        return "cutoff", supply, Fraction(0)
    out_sat = supply - CS_AMP_RD * CS_AMP_BETA / 2 * vov ** 2
    if out_sat >= vov:
        return "saturation", out_sat, -(CS_AMP_BETA / 2 * vov ** 2)
    # Triode: (beta/2) v^2 - (beta vov + 1/RD) v + supply/RD = 0, physical
    # root is the smaller one (v <= vov).
    a = CS_AMP_BETA / 2
    b = CS_AMP_BETA * vov + Fraction(1) / CS_AMP_RD
    c = supply / CS_AMP_RD
    out = (float(b) - math.sqrt(float(b * b - 4 * a * c))) / (2 * float(a))
    return "triode", out, -(float(supply) - out) / float(CS_AMP_RD)


def exact_sqrt(value):
    """Fraction square root when it is exact, else float."""
    num = math.isqrt(value.numerator)
    den = math.isqrt(value.denominator)
    if num * num == value.numerator and den * den == value.denominator:
        return Fraction(num, den)
    return math.sqrt(float(value))


def predicted_dp(supply, vinp, vinn):
    """Exact operating point of the matched differential pair.

    Mirrors the proved window analysis (diffPair_dc_op /
    diffPair_dc_transfer_realizable): common overdrive
    u = sqrt(I_TAIL/beta - d^2/4), outputs VDD - RD*beta/2*(u +- d/2)^2,
    tail = cm - VTO - u. Asserts the case sits inside the proved conduction
    and saturation windows; the harness only commits window cases (the
    fully-switched region is future work). Values are exact Fractions when
    the design makes u rational (the balanced and 3-4-5 rows), floats
    otherwise. The supply branch current is -I_TAIL identically: the ideal
    tail source pins the summed drain currents.
    """
    cm = (vinp + vinn) / 2
    d = vinp - vinn
    ratio = DP_ITAIL / DP_BETA
    if not d * d < 2 * ratio:
        raise RuntimeError(f"diff-pair case outside conduction window: d={d}")
    sqrt_ratio = exact_sqrt(ratio)
    if cm + abs(d) / 2 + DP_RD * DP_BETA / 2 * (sqrt_ratio + abs(d) / 2) ** 2 \
            > supply + DP_VTO:
        raise RuntimeError(
            f"diff-pair case outside saturation window: cm={cm}, d={d}")
    u = exact_sqrt(ratio - d * d / 4)
    if isinstance(u, Fraction):
        outp = supply - DP_RD * DP_BETA / 2 * (u + d / 2) ** 2
        outn = supply - DP_RD * DP_BETA / 2 * (u - d / 2) ** 2
        tail = cm - DP_VTO - u
    else:
        outp = float(supply) - float(DP_RD * DP_BETA) / 2 * (u + float(d) / 2) ** 2
        outn = float(supply) - float(DP_RD * DP_BETA) / 2 * (u - float(d) / 2) ** 2
        tail = float(cm - DP_VTO) - u
    return outp, outn, tail, -DP_ITAIL


def predicted_vod(d):
    """The proved large-signal differential transfer (diff_pair_vod):
    vod(d) = -RD*beta*d*sqrt(I_TAIL/beta - d^2/4) = -4*d*sqrt(1 - d^2/4)."""
    return -float(DP_RD * DP_BETA) * float(d) * \
        math.sqrt(float(DP_ITAIL / DP_BETA) - float(d) ** 2 / 4)


def cs_sources(supply, vin):
    return [f"vdd vdd 0 dc {float(supply):.9g}",
            f"vin in 0 dc {float(vin):.9g}"]


def dp_sources(supply, vinp, vinn):
    return [f"vdd vdd 0 dc {float(supply):.9g}",
            f"vip inp 0 dc {float(vinp):.9g}",
            f"vin inn 0 dc {float(vinn):.9g}"]


def dp_sweep_sources(supply, cm, d):
    """Differential-coordinate drive: sweeping vd moves inp/inn by +-d/2
    around the common mode, sweeping vcm moves both together — the exact
    parametrization of diff_pair_gain / diff_pair_cmrr. Plain VCVS
    stacking, accepted by both simulators."""
    return [f"vdd vdd 0 dc {float(supply):.9g}",
            f"vcm cmnode 0 dc {float(cm):.9g}",
            f"vd dnode 0 dc {float(d):.9g}",
            "eip inp cmnode dnode 0 0.5",
            "ein inn cmnode dnode 0 -0.5"]


def materialize(case, directory, name, sources, analysis_lines):
    source = (ROOT / case["source"]).read_text()
    bench = re.sub(
        r"(?im)^\.end\s*$",
        "\n".join([*sources, TIGHT_OPTIONS, *analysis_lines, ".end"]),
        source,
        count=1,
    )
    deck = directory / f"{name}.cir"
    deck.write_text(bench)
    return deck


def sweep_grid(lo, hi, step):
    """Exact rational sweep grid; the step must tile the interval."""
    count = (hi - lo) / step
    if count.denominator != 1:
        raise RuntimeError(f"sweep step {step} does not tile [{lo}, {hi}]")
    return [lo + index * step for index in range(count.numerator + 1)]


class Ngspice:
    name = "ngspice"
    branch_note = "vdd#branch"

    def __init__(self):
        self.exe = ngspice_path()

    def branch(self, source):
        return f"{source}#branch"

    def _run(self, deck):
        run = subprocess.run([self.exe, "-b", str(deck)], cwd=ROOT,
                             check=True, capture_output=True, text=True)
        return run.stdout + run.stderr

    def op_values(self, case, directory, name, sources, probes):
        deck = materialize(case, directory, name, sources, [".op"])
        text = self._run(deck)
        values = {}
        for probe in probes:
            match = re.search(
                rf"(?im)^\s*{re.escape(probe)}\s+"
                rf"([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[-+]?\d+)?)\s*$", text)
            if not match:
                raise RuntimeError(f"ngspice output has no value for {probe}")
            values[probe] = float(match.group(1))
        return values

    def sweep(self, case, directory, name, sources, sweep_source,
              grid, probes):
        data = directory / f"{name}.{self.name}.txt"
        analysis = [
            ".control",
            f"dc {sweep_source} {float(grid[0]):.9g} {float(grid[-1]):.9g} "
            f"{float(grid[1] - grid[0]):.9g}",
            f"wrdata {data} " + " ".join(f"v({probe})" for probe in probes),
            ".endc",
        ]
        deck = materialize(case, directory, f"{name}-{self.name}",
                           sources, analysis)
        self._run(deck)
        rows = []
        for line in data.read_text().splitlines():
            fields = [float(token) for token in line.split()]
            if not fields:
                continue
            if len(fields) != 2 * len(probes):
                raise RuntimeError(f"unexpected wrdata row width in {data}")
            for x_column in fields[0::2]:
                if abs(x_column - fields[0]) > 1e-9:
                    raise RuntimeError(f"wrdata sweep columns disagree: {line}")
            rows.append((fields[0], dict(zip(probes, fields[1::2]))))
        return finish_sweep(rows, grid, probes)


class Spectre:
    name = "spectre"
    branch_note = "vdd:p"

    def __init__(self):
        self.exe = spectre_path()

    def branch(self, source):
        return f"{source}:p"

    def _run(self, deck, directory):
        raw = directory / f"{deck.stem}.raw"
        run = subprocess.run(
            [self.exe, "-log", "-format", "nutascii", "-raw", str(raw),
             "-outdir", str(directory), str(deck)],
            cwd=ROOT, capture_output=True, text=True, timeout=120)
        if run.returncode != 0:
            raise RuntimeError(
                f"Spectre failed for {deck}:\n{run.stdout}\n{run.stderr}")
        return spectre_test.parse_nutascii(raw)

    def op_values(self, case, directory, name, sources, probes):
        deck = materialize(case, directory, name, sources, [".op"])
        names, rows = self._run(deck, directory)
        if len(rows) != 1:
            raise RuntimeError(f"expected one DC point, found {len(rows)}")
        values = dict(zip(names, rows[0]))
        return {probe: values[probe.lower()] for probe in probes}

    def sweep(self, case, directory, name, sources, sweep_source,
              grid, probes):
        analysis = [
            f".dc {sweep_source} {float(grid[0]):.9g} "
            f"{float(grid[-1]):.9g} {float(grid[1] - grid[0]):.9g}"]
        deck = materialize(case, directory, f"{name}-{self.name}",
                           sources, analysis)
        names, raw_rows = self._run(deck, directory)
        columns = {}
        for probe in probes:
            if probe.lower() not in names:
                raise RuntimeError(f"Spectre sweep has no column {probe}")
            columns[probe] = names.index(probe.lower())
        rows = [(row[0], {probe: row[column]
                          for probe, column in columns.items()})
                for row in raw_rows]
        return finish_sweep(rows, grid, probes)


def finish_sweep(rows, grid, probes):
    """Validate the simulator's sweep against the exact rational grid and
    return {exact_x: {probe: float}}."""
    if len(rows) != len(grid):
        raise RuntimeError(
            f"sweep returned {len(rows)} points, expected {len(grid)}")
    values = {}
    for exact, (x, row) in zip(grid, rows):
        if abs(x - float(exact)) > 1e-6:
            raise RuntimeError(f"sweep point {x} != expected {float(exact)}")
        values[exact] = row
    return values


def close(expected, measured):
    return math.isclose(float(expected), measured, rel_tol=1e-6, abs_tol=1e-9)


def emit(name, checks, failures):
    for probe, expected, actual, ok in checks:
        failures += not ok
        verdict = "MATCH" if ok else "MISMATCH"
        expected_text = (str(expected) if isinstance(expected, (str, Fraction))
                         else f"{expected:.9g}")
        actual_text = (str(actual) if isinstance(actual, str)
                       else f"{float(actual):.9g}")
        print(f"{name + '/' + probe:38} {expected_text:>16} "
              f"{actual_text:>16}  {verdict}")
    return failures


def cs_amp_case(case, directory, sim, failures):
    supply = Fraction(case["supply"])
    vin = Fraction(case["input"])
    region, out, current = predicted_op(supply, vin)
    checks = [("region", case["region"], region, region == case["region"])]
    if case["expect_out"] is not None:
        # The committed table must agree with the closed form.
        checks.append(("table-out", Fraction(case["expect_out"]), out,
                       Fraction(case["expect_out"]) == out))
    if case["expect_supply_current"] is not None:
        checks.append(
            ("table-current", Fraction(case["expect_supply_current"]),
             current,
             Fraction(case["expect_supply_current"]) == current))
    branch = sim.branch("vdd")
    measured = sim.op_values(case, directory, case["name"],
                             cs_sources(supply, vin), ["out", branch])
    checks.append(("out", out, measured["out"], close(out, measured["out"])))
    checks.append((branch, current, measured[branch],
                   close(current, measured[branch])))
    return emit(case["name"], checks, failures), None


def diff_pair_case(case, directory, sim, failures):
    supply = Fraction(case["supply"])
    vinp = Fraction(case["inputp"])
    vinn = Fraction(case["inputn"])
    outp, outn, tail, current = predicted_dp(supply, vinp, vinn)
    checks = []
    for probe, expect_key, predicted in [
            ("outp", "expect_outp", outp), ("outn", "expect_outn", outn),
            ("tail", "expect_tail", tail)]:
        if case.get(expect_key) is not None:
            # The committed table must agree with the closed form.
            checks.append((f"table-{probe}", Fraction(case[expect_key]),
                           predicted, Fraction(case[expect_key]) == predicted))
    checks.append(("table-current", Fraction(case["expect_supply_current"]),
                   current,
                   Fraction(case["expect_supply_current"]) == current))
    branch = sim.branch("vdd")
    measured = sim.op_values(case, directory, case["name"],
                             dp_sources(supply, vinp, vinn),
                             ["outp", "outn", "tail", branch])
    for label, predicted in [("outp", outp), ("outn", outn), ("tail", tail),
                             (branch, current)]:
        checks.append((label, predicted, measured[label],
                       close(predicted, measured[label])))
    return emit(case["name"], checks, failures), measured


def diff_pair_gain_case(case, directory, sim, failures):
    """Central difference across balance against the PROVED derivative.

    diff_pair_gain proves d(voutp - voutn)/dd = -RD*beta*sqrt(I_TAIL/beta)
    = -4 exactly at d = 0. The central difference of the proved transfer
    curve at half-width h is EXACTLY -4*sqrt(1 - h^2/4) (the curve is odd
    in d), so both the difference quotient and its O(h^2) bias are
    predicted in closed form.
    """
    supply = Fraction(case["supply"])
    cm = Fraction(case["cm"])
    h = Fraction(case["h"])
    gain = -DP_RD * DP_BETA * exact_sqrt(DP_ITAIL / DP_BETA)
    vods = []
    for sign, suffix in [(1, "-pos"), (-1, "-neg")]:
        vinp = cm + sign * h / 2
        vinn = cm - sign * h / 2
        outp, outn, _tail, _current = predicted_dp(supply, vinp, vinn)
        measured = sim.op_values(case, directory, case["name"] + suffix,
                                 dp_sources(supply, vinp, vinn),
                                 ["outp", "outn"])
        vods.append(measured["outp"] - measured["outn"])
        predicted = float(outp) - float(outn)
        if not close(predicted, vods[-1]):
            failures = emit(case["name"], [
                (f"vod{suffix}", predicted, vods[-1], False)], failures)
    cdiff = (vods[0] - vods[1]) / (2 * float(h))
    expected_cdiff = float(gain) * math.sqrt(1 - float(h) ** 2 / 4)
    tolerance = float(Fraction(case["tolerance"]))
    checks = [
        ("table-gain", Fraction(case["expect_gain"]), gain,
         Fraction(case["expect_gain"]) == gain),
        ("central-diff", expected_cdiff, cdiff,
         close(expected_cdiff, cdiff)),
        (f"|cdiff-({case['expect_gain']})|<={case['tolerance']}",
         f"<= {tolerance:g}", abs(cdiff - float(gain)),
         abs(cdiff - float(gain)) <= tolerance),
    ]
    return emit(case["name"], checks, failures), None


def cs_amp_gain_sweep_case(case, directory, sim, failures):
    """Measured small-signal gain vs the proved interval AND the nominal.

    Sweeps the proved tolerance-box window around the bias, checks every
    point against the proved transfer curve, then finite-differences the
    measurement. cs_amp_gain_deriv proves the nominal gain is exactly
    -beta*(bias - VTO)*RD = -24/5; because the proved transfer curve is
    quadratic, its central difference equals the derivative EXACTLY, so
    the measured quotient has no discretization bias to excuse — only
    solver noise. cs_amp_gain_interval proves every part in the +-10% box
    has its gain inside [-726/125, -486/125]; the measured gain of the
    (nominal) simulated part must land inside it.
    """
    supply = Fraction(case["supply"])
    bias = Fraction(case["bias"])
    h = Fraction(case["h"])
    step = Fraction(case["step"])
    grid = sweep_grid(bias - h, bias + h, step)
    nominal = -CS_AMP_BETA * (bias - CS_AMP_VTO) * CS_AMP_RD
    # Recompute the proved box corners (commonSource_gain_box instantiated
    # in cs_amp_gain_interval); the committed table must agree.
    fast = -(CS_AMP_BETA * (1 + CS_AMP_BOX)) * \
        (bias - CS_AMP_VTO * (1 - CS_AMP_BOX)) * CS_AMP_RD
    slow = -(CS_AMP_BETA * (1 - CS_AMP_BOX)) * \
        (bias - CS_AMP_VTO * (1 + CS_AMP_BOX)) * CS_AMP_RD
    values = sim.sweep(case, directory, case["name"],
                       cs_sources(supply, bias), "vin", grid, ["out"])
    worst = max(
        abs(values[vin]["out"] - float(predicted_op(supply, vin)[1]))
        for vin in grid)
    model_ok = all(
        close(predicted_op(supply, vin)[1], values[vin]["out"])
        for vin in grid)
    measured_gain = (values[bias + h]["out"] - values[bias - h]["out"]) \
        / (2 * float(h))
    tolerance = float(Fraction(case["nominal_tolerance"]))
    gain_lo = Fraction(case["gain_lo"])
    gain_hi = Fraction(case["gain_hi"])
    checks = [
        ("table-gain", Fraction(case["expect_gain"]), nominal,
         Fraction(case["expect_gain"]) == nominal),
        ("table-gain-lo", gain_lo, fast, gain_lo == fast),
        ("table-gain-hi", gain_hi, slow, gain_hi == slow),
        (f"transfer-curve[{len(grid)}pts]", "max err", worst, model_ok),
        ("measured-gain", nominal, measured_gain,
         abs(measured_gain - float(nominal)) <= 1e-5),
        (f"gain in [{gain_lo},{gain_hi}]",
         f"[{float(gain_lo):g},{float(gain_hi):g}]", measured_gain,
         float(gain_lo) <= measured_gain <= float(gain_hi)),
        (f"|gain-({case['expect_gain']})|<={case['nominal_tolerance']}",
         f"<= {tolerance:g}", abs(measured_gain - float(nominal)),
         abs(measured_gain - float(nominal)) <= tolerance),
    ]
    return emit(case["name"], checks, failures), None


def cs_amp_clipping_case(case, directory, sim, failures):
    """Rail-to-rail sweep against the proved three-region structure.

    cs_amp_regions proves the DC characteristic is: output = VDD on
    input <= VTO (cutoff clipping), the saturation parabola on the window,
    and the closed-form triode root beyond it. The measured structure is
    asserted directly: plateau at the top rail, strict monotone fall past
    threshold, low-rail approach (bounded below by 0 — the proved channel
    admissibility law — and above by the case bound); every sweep point is
    additionally checked against the region-wise closed form, and the
    vin = 7/2 point against the exact rational 5/12 (cs_amp_triode_point).
    """
    supply = Fraction(case["supply"])
    grid = sweep_grid(Fraction(case["sweep_lo"]), Fraction(case["sweep_hi"]),
                      Fraction(case["step"]))
    values = sim.sweep(case, directory, case["name"],
                       cs_sources(supply, grid[0]), "vin", grid, ["out"])
    measured = [values[vin]["out"] for vin in grid]
    plateau = [vin for vin in grid if vin <= CS_AMP_VTO]
    plateau_worst = max(abs(values[vin]["out"] - float(supply))
                        for vin in plateau)
    plateau_ok = all(close(supply, values[vin]["out"]) for vin in plateau)
    falling = [values[vin]["out"] for vin in grid if vin >= CS_AMP_VTO]
    monotone_ok = all(later < earlier
                      for earlier, later in zip(falling, falling[1:]))
    worst = max(abs(values[vin]["out"] - float(predicted_op(supply, vin)[1]))
                for vin in grid)
    model_ok = all(close(predicted_op(supply, vin)[1], values[vin]["out"])
                   for vin in grid)
    regions = [predicted_op(supply, vin)[0] for vin in grid]
    structure = [region for index, region in enumerate(regions)
                 if index == 0 or regions[index - 1] != region]
    probe_vin = Fraction(case["triode_probe_input"])
    probe_out = Fraction(case["triode_probe_output"])
    low_rail = Fraction(case["low_rail_bound"])
    final = measured[-1]
    checks = [
        ("regions", "cutoff>sat>triode", ">".join(
            {"cutoff": "cutoff", "saturation": "sat",
             "triode": "triode"}[region] for region in structure),
         structure == ["cutoff", "saturation", "triode"]),
        (f"plateau[vin<={CS_AMP_VTO}]", float(supply), plateau_worst,
         plateau_ok),
        (f"monotone-fall[{len(falling)}pts]", "strictly decreasing",
         "decreasing" if monotone_ok else "NOT monotone", monotone_ok),
        (f"model[{len(grid)}pts]", "max err", worst, model_ok),
        (f"triode@{probe_vin}", probe_out, values[probe_vin]["out"],
         close(probe_out, values[probe_vin]["out"])),
        (f"low-rail@{grid[-1]}", f"in (0, {float(low_rail):g}]", final,
         0 < final <= float(low_rail)),
    ]
    return emit(case["name"], checks, failures), None


def dp_diff_sweep_case(case, directory, sim, failures):
    """Differential sweep vs the proved large-signal transfer and gain.

    Sweeps the differential drive across the proved window and checks:
    every point against the proved odd transfer -4*d*sqrt(1 - d^2/4)
    (diff_pair_vod), the odd symmetry itself, and the central difference
    at balance against the proved derivative -4 (diff_pair_gain) with the
    closed-form O(h^2) bias -4*sqrt(1 - h^2/4) of the proved curve.
    """
    supply = Fraction(case["supply"])
    cm = Fraction(case["cm"])
    d_max = Fraction(case["d_max"])
    step = Fraction(case["step"])
    grid = sweep_grid(-d_max, d_max, step)
    for d in (-d_max, Fraction(0), d_max):  # window guard, exact arithmetic
        predicted_dp(supply, cm + d / 2, cm - d / 2)
    values = sim.sweep(case, directory, case["name"],
                       dp_sweep_sources(supply, cm, 0), "vd", grid,
                       ["outp", "outn"])
    vod = {d: values[d]["outp"] - values[d]["outn"] for d in grid}
    worst = max(abs(vod[d] - predicted_vod(d)) for d in grid)
    model_ok = worst <= float(Fraction(case["curve_tolerance"]))
    symmetry = max(abs(vod[d] + vod[-d]) for d in grid)
    symmetry_ok = symmetry <= float(Fraction(case["symmetry_tolerance"]))
    gain = -DP_RD * DP_BETA * exact_sqrt(DP_ITAIL / DP_BETA)
    cdiff = (vod[step] - vod[-step]) / (2 * float(step))
    expected_cdiff = float(gain) * math.sqrt(1 - float(step) ** 2 / 4)
    tolerance = float(Fraction(case["gain_tolerance"]))
    checks = [
        ("table-gain", Fraction(case["expect_gain"]), gain,
         Fraction(case["expect_gain"]) == gain),
        (f"vod-curve[{len(grid)}pts]",
         f"<= {float(Fraction(case['curve_tolerance'])):g}", worst, model_ok),
        (f"odd-symmetry[{len(grid)}pts]",
         f"<= {float(Fraction(case['symmetry_tolerance'])):g}", symmetry,
         symmetry_ok),
        ("central-diff", expected_cdiff, cdiff,
         abs(cdiff - expected_cdiff) <= tolerance),
        (f"|cdiff-({case['expect_gain']})|<={case['gain_tolerance']}",
         f"<= {tolerance:g}", abs(cdiff - float(gain)),
         abs(cdiff - float(gain)) <= tolerance),
    ]
    return emit(case["name"], checks, failures), None


def dp_cm_sweep_case(case, directory, sim, failures):
    """Common-mode sweep: near-invariance of the outputs in floating
    point; the proof (diff_pair_balanced / diff_pair_cmrr) says EXACT
    invariance at the ideal model. The tail must track cm - VTO - u."""
    supply = Fraction(case["supply"])
    d = Fraction(case["d"])
    grid = sweep_grid(Fraction(case["cm_lo"]), Fraction(case["cm_hi"]),
                      Fraction(case["step"]))
    outp_model, outn_model, _tail, _current = predicted_dp(
        supply, grid[0] + d / 2, grid[0] - d / 2)
    predicted_dp(supply, grid[-1] + d / 2, grid[-1] - d / 2)  # window guard
    values = sim.sweep(case, directory, case["name"],
                       dp_sweep_sources(supply, grid[0], d), "vcm", grid,
                       ["outp", "outn", "tail"])
    tolerance = float(Fraction(case["invariance_tolerance"]))
    spread = {
        probe: max(values[cm][probe] for cm in grid) -
        min(values[cm][probe] for cm in grid)
        for probe in ("outp", "outn")}
    u = exact_sqrt(DP_ITAIL / DP_BETA - d * d / 4)
    tail_worst = max(
        abs(values[cm]["tail"] - (float(cm - DP_VTO) - float(u)))
        for cm in grid)
    checks = [
        (f"outp-invariance[{len(grid)}pts]", f"<= {tolerance:g}",
         spread["outp"], spread["outp"] <= tolerance),
        (f"outn-invariance[{len(grid)}pts]", f"<= {tolerance:g}",
         spread["outn"], spread["outn"] <= tolerance),
        ("outp-level", outp_model, values[grid[0]]["outp"],
         close(outp_model, values[grid[0]]["outp"])),
        ("outn-level", outn_model, values[grid[0]]["outn"],
         close(outn_model, values[grid[0]]["outn"])),
        (f"tail-tracks-cm[{len(grid)}pts]", "max err", tail_worst,
         tail_worst <= tolerance),
    ]
    return emit(case["name"], checks, failures), None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sim", choices=("ngspice", "spectre"),
                        default="ngspice")
    arguments = parser.parse_args()
    sim = Ngspice() if arguments.sim == "ngspice" else Spectre()
    cases = json.loads(CASES.read_text())
    failures = 0
    print(f"{'case/probe':38} {'Lean exact':>16} {sim.name:>16}  verdict")
    print("-" * 82)
    handlers = {
        "cs_amp": cs_amp_case,
        "diff_pair": diff_pair_case,
        "diff_pair_gain": diff_pair_gain_case,
        "cs_amp_gain_sweep": cs_amp_gain_sweep_case,
        "cs_amp_clipping": cs_amp_clipping_case,
        "dp_diff_sweep": dp_diff_sweep_case,
        "dp_cm_sweep": dp_cm_sweep_case,
    }
    invariance = {}
    with tempfile.TemporaryDirectory(prefix="leanmodels-amp-") as tmp:
        directory = Path(tmp)
        for case in cases:
            handler = handlers[case.get("topology", "cs_amp")]
            failures, measured = handler(case, directory, sim, failures)
            if case.get("invariance_group") and measured is not None:
                invariance.setdefault(case["invariance_group"], []).append(
                    (case["name"], measured))
    # Ideal-tail CMRR: measured outputs of every case in an invariance group
    # must agree with each other (diff_pair_cmrr: common-mode shifts move
    # the tail node only), independently of the table values.
    for group, rows in invariance.items():
        (name0, first), rest = rows[0], rows[1:]
        for name, measured in rest:
            for label in ("outp", "outn"):
                ok = close(first[label], measured[label])
                failures = emit(
                    f"cmrr[{group}]",
                    [(f"{label}:{name0}=={name}", first[label],
                      measured[label], ok)],
                    failures)
    print("-" * 82)
    print(f"{len(cases)} cases against {sim.name}: {failures} failed checks")
    raise SystemExit(1 if failures else 0)


if __name__ == "__main__":
    main()
