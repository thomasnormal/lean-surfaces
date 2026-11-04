# Amplifier demo: proving a real amplifier from the MOS1 device laws

The analog lane's amplifier campaign proves theorems about real amplifier
topologies FROM the MOS1 device equations — operating points as exact
rationals, small-signal gain as a literal derivative of a derived transfer
curve, clipping, and tolerance intervals — such that the predictions match
ngspice measurement now and bench measurement later. The measurement
ladder has two rungs: rung 1 (simulator, closed below) and rung 2 (bench,
protocol below).

## Capability honesty

These are FOCUSED examples in the `loaded_inverter` style, not generic
compilation. Each stage ships a checked deck adapter
(`ElaboratedCircuit.toCommonSourceNominal`, ...) that accepts exactly one
committed topology in the restricted MOS1 profile (`LEVEL=1`, `LAMBDA=0`,
`IS=0`, positive `VTO`/`KP`) and rejects everything else. The behavior
relations are written per-topology; nothing here claims to compile arbitrary
netlists into physics relations.

| axis | amp-lane status |
|---|---|
| parsed | shared front end — both decks load through the lane's SPICE parser (`load_circuit`), which is generic |
| typed | FOCUSED — `toCommonSourceNominal` / `toDiffPairNominal` adapters accept exactly one committed topology each and reject everything else |
| device law | shared — the restricted MOS1 profile (`LEVEL=1`, `LAMBDA=0`, `IS=0`) from `LeanModels/Spice/Mos1.lean`, reused from the loaded-inverter work |
| assembly | FOCUSED — `CommonSourceDC` / `DiffPairDC` are hand-written per-topology KCL relations; no netlist-to-physics compiler is claimed |
| automation | partial — spec statements close by the `proofs` tactic, but the nonlinear solves underneath are hand-structured library lemmas (`nlinarith` hints, IVT existence, monotone uniqueness) |
| examples | 2 topologies, 43 spec theorems (28 common-source + 15 diff-pair), each pinned to exactly `[propext, Classical.choice, Quot.sound]` |

Two standing design laws hold throughout:

1. **Realizability pairing** — every safety/behavior theorem ships with a
   realizability twin (see the pairing table below).
2. **Spec-in-behavior ban** — behavior relations contain only device
   equations, KCL, topology, and environment. Operating-point values, the
   transfer curve, and the saturation window are all *derived* in the
   Specification layer; the proofs solve the nonlinear KCL system, they do
   not retrieve asserted answers.

## Stage 1: resistor-loaded NMOS common-source amplifier

* Deck: `Examples/spice/cs_amp/cs_amp.cir` — testbench-free component with
  ports `in` (gate), `out` (drain), `vdd`, ground. Supply and input drivers
  belong to the run environment (the DRAM lesson: decks are reusable
  components, not testbenches).
* Library: `LeanModels/Spice/CommonSource.lean`.
* Example proofs: `Examples/spice/cs_amp/{proof,spec}.lean`.
* Harness: `harness/spice/amp_test.py` + `amp_cases.json`
  (`tools/ci.sh` steps `spice-amp-ngspice` and, when the licensed binary
  is present, `spice-amp-spectre`) — see "Closing the loop, rung 1" below.

### Bias designed for provability

`VDD = 5`, `VTO = 1`, `KP = 400u` (`W/L = 1`, so `β = 1/2500 A/V²`),
`RD = 12k`, so `β·RD = 24/5`. The saturation branch of the square law meets
the resistor load line at

```
Vout(Vin) = VDD − (β·RD/2)·(Vin − VTO)² = 5 − (12/5)·(Vin − 1)².
```

The edge of saturation solves the square-law-meets-load-line quadratic
`(β·RD/2)·Vov² + Vov − VDD = 0`, i.e. `12·Vov² + 5·Vov − 25 = 0`, whose
discriminant `25 + 1200 = 1225 = 35²` is a perfect square **by design** —
so the window endpoint is exactly rational: `Vov* = 5/4`, `v_hi = 9/4`.
At the designed bias `V_in0 = 2`: `I_D = 200 µA` and `V_out0 = 13/5 V`
exactly. The derivative of the derived transfer curve at the bias is
`−β·RD·(V_in0 − VTO) = −24/5`, the small-signal gain target for the gain
campaign. All of this arithmetic is re-checked by kernel-decidable
`#guard`s in `proof.lean`/`spec.lean` and cross-checked against ngspice by
the harness (at tightened solver tolerances ngspice agrees with the exact
rationals to 7+ digits; the triode point beyond the window matches the
irrational closed-form root `(53 − √1609)/24` in floating point).

### The behavior relation (physics only)

`CommonSourceDC fabricated supply input output` says exactly:

* `0 ≤ output` — the NMOS channel-orientation admissibility law
  (`Mos1DeviceLaw` with the source at ground), and
* `(supply − output)/R_D = mos1ForwardCurrent … input output` — KCL at the
  drain node with the resistor Ohm law and the MOS1 piecewise channel law
  substituted for the two branch currents.

No voltage values, no gain, no region tags. `CommonSourceBehavior` wraps
this as a lane `Behavior` over `RunWorld` instances/environments.

### Theorems and realizability pairing

| behavior/safety theorem | realizability twin |
|---|---|
| `cs_amp_op` — every DC state at the designed bias has `output = 13/5`, derived by solving the piecewise KCL in-proof | `cs_amp_op_realizable` — `13/5` *is* a DC state |
| `cs_amp_transfer` — on `[3/2, 9/4]` every DC state satisfies `output = 5 − (12/5)(input−1)²` | `cs_amp_transfer_realizable` — the transfer point is a DC state for every window input |
| `cs_amp_saturation` — on `[3/2, 9/4]` every DC state is saturated (`V_ds ≥ V_ov`), the validity domain for gain work | `cs_amp_dc_exists` — an operating point exists for **every** input (IVT) |
| `cs_amp_cutoff` — clipping: `input ≤ 1` forces `output = 5` | `cs_amp_dc_exists` |
| `cs_amp_dc_unique` — the operating point is unique at every input | `cs_amp_dc_exists` |

Library-level, the same pairing is stated against the run-world framework:
`commonSource_saturation_safe` (`SafeUnder`) with
`commonSource_saturation_realizable`/`commonSource_realizable`
(`RealizableUnder`), plus `commonSource_determinate` (`DeterminateUnder`).
All spec theorems close under `[propext, Classical.choice, Quot.sound]`
only.

### How the nonlinear solve works (first in the lane)

`commonSource_dc_op` performs the operating-point derivation from the
physics conjuncts:

1. Cutoff branch is excluded by the window hypothesis `VTO < input`.
2. On the **triode branch** (`output ≤ V_ov`) the KCL equation is the
   quadratic `β(V_ov·v − v²/2) = (V_DD − v)/R_D`. The proof multiplies out
   the division (`div_eq_iff`), then `nlinarith` with the single hint
   `0 ≤ β·R_D·(V_ov − v)²` squeezes `V_ov ≤ output` against the window
   inequality; with the branch bound this pins `output = V_ov`, the branch
   boundary, where the equation collapses to the saturation value.
3. On the **saturation branch** the equation is linear in `output` and
   `linear_combination -hkcl` closes it.

Uniqueness (`commonSource_dc_determinate`) is the monotone argument: the
channel current is monotone in `V_ds` when `LAMBDA = 0`
(`mos1ForwardCurrent_mono_drop`, proved branch-by-branch with `nlinarith`)
while the load line is strictly decreasing. Existence
(`commonSource_dc_exists`) is IVT over ℝ applied to the branch-glued
continuous current, reusing `mos1EnvelopeCurrent` and its continuity from
the loaded-inverter work.

### Evidence layer

`commonSourceHarnessEvidence` (`EvidenceRecord`, modality
`finiteValidation`) records the ngspice differential harness.
`commonSourceEnvelopeClaim`/`commonSourceAcceptedValidity` bind a physical
DC relation to the MOS1 envelope on the saturation window; accepting the
claim requires an explicit proof or calibration hypothesis — bench
measurement later supplies it. Metadata alone cannot construct
`AcceptedValidity`. The bench protocol below shows the intended
instantiation.

## Stage 1b: tolerance-box gain interval (the Monte-Carlo killer)

Fabricated parts do not hit nominal `VTO`/`KP`. `cs_amp_gain_interval`
quantifies over EVERY part in a ±10 % box — `VTO ∈ [0.9, 1.1]` V,
`KP ∈ [360µ, 440µ]` A/V² — and proves, for any solution family of the
physics-only DC relation on the ±50 mV window around the 2 V bias:

* the family has a literal derivative at the bias, the part's own gain
  `−KP·(2 − VTO)·R_D`;
* that gain lies in the closed interval `[−726/125, −486/125] =
  [−5.808, −3.888]`;
* the device is saturated there, re-derived per-part from ONE worst-corner
  window check (`commonSource_window_box`: highest `β`, lowest `VTO`
  dominates the window inequality for the whole box — the nominal window
  endpoint 9/4 does *not* survive the box, which is why the interval
  theorem lives on the shrunken window `(39/20, 41/20)`; a `#guard` pins
  the failing corner);
* the DC output lies in `[2257/1250, 4063/1250] = [1.8056, 3.2504]` V.

Where Monte-Carlo samples the box, the theorem covers it. The interval is
honest — `cs_amp_gain_interval_realizable` shows the hypothesis is never
vacuous anywhere in the box, and `cs_amp_gain_interval_tight_fast`/`_slow`
show both endpoints are attained by the corner parts. **This interval is
the bench-measurement prediction**: a measured gain or operating point
outside it falsifies the model envelope.

## Stage 2: matched differential pair with ideal tail source

* Deck: `Examples/spice/diff_pair/diff_pair.cir` — two matched NMOS
  (one shared `.model` card), shared tail node, matched 10k drain
  resistors, IDEAL tail current source `I_TAIL = 400µ`. Ports `inp`,
  `inn`, `outp`, `outn`, `vdd`, ground; testbench-free.
* Library: `LeanModels/Spice/DiffPair.lean`. Each drain equation is
  EXACTLY a common-source stage shifted by the tail voltage
  (`diffPairDC_iff`), so the entire Stage-1 solve library is reused per
  side; the tail node is pinned by a two-sided monotone argument
  (`mos1ForwardCurrent_mono_gate`/`_strict_mono_gate`).
* Example proofs: `Examples/spice/diff_pair/{proof,spec}.lean`.
* Harness rows: `dp-balanced`, `dp-cm-shift` (with a cross-run CMRR
  invariance check), `dp-probe-345`, `dp-gain-central-diff`, plus the
  sweep rows `dp-diff-sweep`, `dp-cm-sweep-balanced`, and
  `dp-cm-sweep-driven` described under rung 1 below.

### Bias designed for provability

`VDD = 5`, `VTO = 1`, `KP = 400µ` (`β = 1/2500`), `RD = 10k`,
`I_TAIL = 400µ`, so `I_TAIL/β = 1 V²` is a perfect square **by design**:
the balanced overdrive is exactly 1 V, both outputs sit at exactly
`VDD − RD·I_TAIL/2 = 3` V, the tail tracks the common mode at exactly
`cm − 2`, and the balance differential gain is exactly
`−β·√(I_TAIL/β)·RD = −4`. The large-signal probe rides the 3-4-5
triangle: `d = 6/5` makes `√(1 − d²/4) = 4/5`, so at `cm = 1/4` (inputs
`17/20`, `−7/20`) the outputs are exactly `27/25` and `123/25`
(`v_od = −96/25`), tail `−31/20`.

### Theorems and realizability pairing

| behavior/safety theorem | realizability twin |
|---|---|
| `diff_pair_balanced` — for every `cm ≤ 4`, every DC state has both outputs at exactly 3 V and `tail = cm − 2` | `diff_pair_balanced_realizable`; `diff_pair_cm_range` packages the whole CM range |
| `diff_pair_gain` — ANY solution family in differential coordinates (`5/2 ± d/2`, `|d| < 1/2`) has literal derivative `−4` of `v_outP − v_outN` at balance | `diff_pair_gain_realizable` |
| `diff_pair_cmrr` — exact common-mode invariance on `cm, cm' ≤ 21/8`, `|d| ≤ 1/2` (see below) | `diff_pair_cmrr_realizable` |
| `diff_pair_vod` — exact large-signal differential transfer `−4·d·√(1 − d²/4)` on the window | `diff_pair_vod_realizable` |
| `diff_pair_probe` — the 3-4-5 probe point, exactly rational | `diff_pair_probe_realizable` |
| `diff_pair_dc_unique` — outputs and tail are unique at every drive | window realizability twins above |

Library-level: `diffPair_balanced_safe` (`SafeUnder`) with
`diffPair_balanced_realizable` (`RealizableUnder`), and
`diffPair_determinate` (`DeterminateUnder`). All spec theorems close under
`[propext, Classical.choice, Quot.sound]` only. The differential window
`|d| ≤ 1/2`, `cm ≤ 21/8` is TIGHT: the worst corner lands the saturation
check at exactly `6 = VDD + VTO` (kernel-checked by `#guard`).

### The CMRR theorem is an idealization, loudly labeled

`diff_pair_cmrr` proves EXACT invariance: shifting the common mode moves
the tail node by exactly the shift and moves neither output at all —
infinite CMRR. This is a *provable idealization*, true under exactly two
premises: `LAMBDA = 0` (saturated channel current independent of `V_DS`)
and the IDEAL tail source (exact `I_TAIL` at any tail voltage, no
compliance limit — there is correspondingly no proved lower CM limit).
Real amplifiers only approximate it; channel-length modulation and finite
tail-source output resistance each break one premise. The theorem's value
is that it states exactly WHAT ideal common-mode rejection is, so later
refinements can quantify the deviation — and the honest framing is the
demo's point. The harness cross-checks the invariance between the
`dp-balanced` and `dp-cm-shift` ngspice runs, sweeps the common mode
across both proved windows asserting near-invariance in floating point,
and checks the proved derivative `−4` against a central difference with
the O(h²) bias of the proved transfer curve itself predicted in closed
form (`−4·√(1 − h²/4)`).

### Feedstock note

The differential-coordinate parametrization (`cm ± d/2`), matched-pair
symmetry, tail-shift invariance, and balance-point analysis in
`DiffPair.lean` are exactly the ingredients the planned
`DifferentialSenseBehavior` work needs for sense-amplifier-style
differential sensing; the module keeps them in library form.

## Closing the loop, rung 1: simulator measurement

`harness/spice/amp_test.py` + `amp_cases.json` measure every proved
prediction against a simulator before anyone solders anything. ci runs it
as `spice-amp-ngspice` (ngspice-46, always when ngspice is installed) and
`spice-amp-spectre` (`--sim spectre`, Cadence Spectre as an independent
second oracle behind the licensed-binary gate; branch currents probed as
`vdd:p` instead of `vdd#branch`). Both simulators are **untrusted
differential oracles**: the Lean theorems do not depend on the comparison,
and agreement does not by itself establish physical model validity — that
is what the evidence layer and rung 2 are for.

Five measurement classes; 15 cases, 85 checks, all green on both
simulators:

1. **Operating points** (`.op` rows) — exact rational OP theorems vs
   simulated node voltages and the supply branch current, at tightened
   solver tolerances. Every expected value in the case table is
   *recomputed from the deck constants inside the harness*, so a drifted
   deck, a drifted case table, or a drifted simulator all fail.
2. **Gain** (`cs-amp-gain-sweep`) — a `.dc` sweep across the proved
   tolerance-box window `(39/20, 41/20)`, every point checked against the
   proved transfer curve, then the measured curve is central-differenced
   at the 2 V bias. The measured gain must land INSIDE the proved interval
   `[−726/125, −486/125]` (`cs_amp_gain_interval`) AND within
   model-accuracy tolerance of the nominal `−β·V_ov·R_D = −24/5`
   (`cs_amp_gain_deriv`). Because the proved transfer curve is a
   quadratic, its central difference equals the derivative EXACTLY — the
   measurement has no discretization bias to excuse, only solver noise.
3. **Clipping** (`cs-amp-clipping-sweep`) — `vin` from ground into the low
   rail; asserts the proved three-region structure (`cs_amp_regions`)
   directly on the measurement: cutoff plateau at `VDD`, strict monotone
   fall past threshold, low-rail approach bounded below by 0 (the proved
   admissibility law) — with every point checked against the region-wise
   closed form and `vin = 7/2` against the exact rational `5/12`
   (`cs_amp_triode_point`).
4. **Differential sweep** (`dp-diff-sweep`) — the drive `d` swept across
   the proved window `|d| ≤ 1/2` via a VCVS differential-coordinate bench
   (`inp/inn = cm ± d/2`, the exact parametrization of the theorems);
   checks the proved large-signal transfer `−4·d·√(1 − d²/4)`
   (`diff_pair_vod`) point by point, the odd symmetry, and the
   central-difference balance gain against the proved `−4`
   (`diff_pair_gain`).
5. **Common-mode sweeps** (`dp-cm-sweep-balanced`, `dp-cm-sweep-driven`) —
   the common mode swept across the proved windows at `d = 0` (`cm ∈
   [2, 4]`, `diff_pair_balanced`) and `d = 1/2` (`cm ∈ [2, 21/8]`,
   `diff_pair_cmrr`); asserts near-invariance of both outputs in floating
   point (the proof says EXACT invariance at the ideal model) plus the
   tail tracking `cm − VTO − u`.

The money numbers (ngspice-46 / Spectre 23.1, tightened tolerances):

| proved prediction | Lean value (exact) | ngspice measures | spectre measures |
|---|---|---|---|
| OP at designed bias (`cs_amp_op`) | `13/5 = 2.6 V` | `2.599999969` | `2.599999969` |
| supply current at bias | `−200 µA` | `−200.000003 µA` | `−200.000003 µA` |
| gain at bias (`cs_amp_gain_deriv`) | `−24/5 = −4.8` | `−4.800000000` | `−4.799999942` |
| gain interval (`cs_amp_gain_interval`) | `[−5.808, −3.888]` | contains −4.8 ✓ | contains −4.8 ✓ |
| clipping plateau (`cs_amp_cutoff`) | `5 V` on `vin ≤ 1` | max dev `6.0e-8` | max dev `6.0e-8` |
| triode point (`cs_amp_triode_point`) | `5/12 ≈ 0.4166667` | `0.416666666` | `0.416666666` |
| three-region curve (`cs_amp_regions`, 81 pts) | region-wise closed form | max err `6.0e-8` | max err `6.0e-8` |
| diff-pair balance (`diff_pair_balanced`) | `3 V` both outputs | `2.999999970` | `3.000000000` |
| diff transfer (`diff_pair_vod`, 101 pts) | `−4·d·√(1 − d²/4)` | max err `2.4e-8` | max err `3.2e-8` |
| balance gain (`diff_pair_gain`), h = 0.01 | `−4` (biased quotient `−3.99995`) | `−3.999949` | `−3.999950` |
| CM invariance (`diff_pair_cmrr`), 41+51 pts | exact (ideal model) | spread ≤ `2.0e-8` | spread ≤ `1.6e-9` |

## Closing the loop, rung 2: measuring this amp on a bench

The physical version of the same experiment. Nothing below changes any
theorem — it changes what the theorems are *about*: the calibration
evidence binds a physical device to the MOS1 envelope, and the interval
theorem instantiated at the fitted parameter box becomes a falsifiable
prediction about a voltmeter reading.

### The two theorems being tested

The nominal gain is a literal derivative derived from the physics-only DC
relation, and the tolerance-box theorem turns it into an interval over
every part in a parameter box:

```lean
-- Examples/spice/cs_amp/spec.lean (excerpt)
theorem cs_amp_gain_deriv {vout : ℝ → ℝ}
    (hsol : ∀ v ∈ Set.Ioo (3 / 2 : ℝ) (9 / 4),
      CommonSourceDC Examples.spice.cs_amp.proof.csAmpInstance
        5 v (vout v)) :
    deriv vout 2 = -(24 / 5) := by proofs
...
theorem cs_amp_gain_interval {vto kp : ℝ} {vout : ℝ → ℝ}
    (hvto : vto ∈ Set.Icc (9 / 10 : ℝ) (11 / 10))
    (hkp : kp ∈ Set.Icc (9 / 25000 : ℝ) (11 / 25000))
    (hsol : ∀ v ∈ Set.Ioo (39 / 20 : ℝ) (41 / 20),
      CommonSourceDC
        { threshold := vto, beta := kp, drainResistance := 12000 }
        5 v (vout v)) :
    HasDerivAt vout (-(kp * (2 - vto) * 12000)) 2 ∧
    -(kp * (2 - vto) * 12000) ∈
      Set.Icc (-(726 / 125) : ℝ) (-(486 / 125)) ∧
    2 - vto ≤ vout 2 ∧
    vout 2 ∈ Set.Icc (2257 / 1250 : ℝ) (4063 / 1250) := by proofs
```

The corner lemmas underneath (`commonSource_gain_box`,
`commonSource_window_box` in `LeanModels/Spice/CommonSource.lean`) are
generic in the box, the bias, the supply, and `R_D` — the spec theorem is
their instantiation at the nominal ±10 % box, and the bench flow
re-instantiates them at the *fitted* box (the corner arithmetic is
kernel-decidable `#guard`s; producing the bench instance is mechanical).

### Suggested device: a 2N7000-class NMOS

A 2N7000/BS170-class small-signal enhancement NMOS (TO-92, breadboardable,
gate-protected) is the right test article because at low drain currents it
behaves **near-long-channel**: above threshold and below the
mobility-degradation bend, its measured `√I_D` vs `V_GS` is straight over
a usable overdrive range — i.e. it approximately satisfies exactly the
square law that `Mos1DeviceLaw` states. Expect `VTO ≈ 1.5–2.5 V` and
`β ≈ 20–100 mA/V²` — far from the deck's provability-designed nominals,
which is the point: the parameters enter as a *fitted box*, not as
assumptions.

### Parameter extraction (the ID–VGS sweep)

1. **Force saturation:** diode-connect the device (drain tied to gate
   through the ammeter, so `V_DS = V_GS`). Then `V_DS ≥ V_GS − VTO`
   whenever the channel conducts — every sweep point is on the saturation
   branch of the MOS1 law.
2. **Sweep:** step `V_GS` from below threshold until `I_D` reaches a few
   mA, 10–20 mV steps, recording `I_D` (bench PSU + DMM is sufficient;
   keep the device cool — pause between points or use a heatsink clip, and
   record the ambient temperature with the data).
3. **Fit window:** plot `√I_D` against `V_GS` and keep the straight
   region only — discard the subthreshold tail at the bottom and the
   mobility-degradation bend at the top. This window IS the model-validity
   domain being claimed.
4. **Least squares** on the saturation region: `√I_D = s·(V_GS − VTO)`,
   so the x-intercept is `VTO_fit` and `β_fit = 2s²` (deck convention
   `I_D = β/2·V_ov²`, `β = KP·W/L`).
5. **Box:** widen the point fit to an interval box
   `VTO ∈ [VTO_fit ± δ_V]`, `β ∈ [β_fit·(1 − δ_β), β_fit·(1 + δ_β)]`
   with `δ` covering fit covariance, instrument error, and temperature
   drift over the measurement session (e.g. `δ_V = 100 mV`,
   `δ_β = 10 %`).

### Re-instantiation at the fitted box

Re-design the bias for the fitted part exactly the way the nominal deck
was designed (the lemmas are parametric; only the `#guard` arithmetic
reruns). Illustrative fit `VTO_fit = 1.9 V`, `β_fit = 50 mA/V²`, box
`VTO ∈ [1.8, 2.0]`, `β ∈ [45, 55] mA/V²`:

* choose overdrive inside the fit window, e.g. `V_ov = 0.5 V` →
  bias `V_in0 = 2.4 V`, `I_D = β/2·V_ov² ≈ 6.3 mA`;
* choose `VDD = 9 V`, `R_D = 680 Ω` (drop ≈ 4.3 V, mid-swing);
* worst-corner window check (`commonSource_window_box`, highest `β`,
  lowest `VTO`, window `±50 mV`):
  `0.055·680/2·(2.45 − 1.8)² + (2.45 − 1.8) = 8.55 ≤ 9` ✓;
* gain corners (`commonSource_gain_box`):
  `gain ∈ [−0.055·(2.4 − 1.8)·680, −0.045·(2.4 − 2.0)·680]
  = [−22.44, −12.24]`.

The interval is wide because `δ_V = 100 mV` is large relative to
`V_ov = 0.5 V` — the theorem is honest about what a sloppy fit buys.
Tighten the fit (or raise `V_ov`) and the interval tightens with it,
corner-exactly.

### The fit enters as an evidence record

This is the lane's actual evidence-layer API — provenance metadata is a
structure, and *acceptance* of a validity claim requires an explicit proof
or hypothesis; metadata alone cannot construct it:

```lean
-- LeanModels/Circuit/Validity.lean (excerpt)
structure EvidenceRecord where
  artifact : String
  artifactHash : String
  version : String
  issuer : String
  modality : CoverageModality
  domainDescription : String
  confidenceDescription : String := ""
  evidenceDate : String := ""
  supersedes : Option String := none
...
structure ValidityClaim
    (World Boundary Internal : Type) where
  physical : Behavior World Boundary Internal
  envelope : Behavior World Boundary Internal
  domain : World → Boundary → Internal → Prop
  statement : Prop :=
    ∀ world boundary internal,
      domain world boundary internal →
      physical world boundary internal →
      envelope world boundary internal
...
structure AcceptedValidity
    (claim : ValidityClaim World Boundary Internal) where
  evidence : EvidenceRecord
  accepted : claim.statement
```

The common-source stage already ships its claim constructor — the envelope
is the behavior relation, the domain is the saturation run window, and the
physical relation stays an explicit parameter:

```lean
-- LeanModels/Spice/CommonSource.lean (excerpt)
def commonSourceEnvelopeClaim
    (physical : Behavior CommonSourceWorld CommonSourceBoundary Unit) :
    ValidityClaim CommonSourceWorld CommonSourceBoundary Unit :=
  { physical
    envelope := CommonSourceBehavior
    domain := fun world _boundary _internal =>
      CommonSourceSaturationRun world }
...
def commonSourceAcceptedValidity
    (physical : Behavior CommonSourceWorld CommonSourceBoundary Unit)
    (haccepted : (commonSourceEnvelopeClaim physical).statement) :
    AcceptedValidity (commonSourceEnvelopeClaim physical) :=
  { evidence := commonSourceHarnessEvidence
    accepted := haccepted }
```

The bench calibration lands as a `.calibration`-modality record plus the
explicit acceptance hypothesis for the fitted unit:

```lean
-- (illustrative — the bench-calibration instance; lands in the tree together with the measurement data)
def bench2N7000Evidence : EvidenceRecord :=
  { artifact := "bench/2n7000/unit-01/id_vgs.csv"
    artifactHash := "sha256:<hash of the raw sweep data>"
    version := "unit-01, 25 °C"
    issuer := "bench"
    modality := .calibration
    domainDescription :=
      "ID–VGS saturation sweep (diode-connected), fit window " ++
      "ID ∈ [0.2, 5] mA: VTO_fit = 1.90 V, β_fit = 50 mA/V²; " ++
      "box VTO ∈ [1.80, 2.00] V, β ∈ [45, 55] mA/V² (3σ + drift)"
    confidenceDescription :=
      "√ID fit residual < 1 % of full scale on the fit window" }

def bench2N7000Validity
    (physical : Behavior CommonSourceWorld CommonSourceBoundary Unit)
    (haccepted : (commonSourceEnvelopeClaim physical).statement) :
    AcceptedValidity (commonSourceEnvelopeClaim physical) :=
  { evidence := bench2N7000Evidence
    accepted := haccepted }
```

`haccepted` is the calibration hypothesis: *this physical unit's DC
behavior, on the fit window, is covered by the MOS1 envelope at the fitted
box*. It is exactly what the sweep supports and exactly what the next step
tests.

### The prediction and the falsification criterion

**Prediction.** Build the amp (fitted unit, `R_D`, `VDD`, bias from the
re-instantiation). The interval theorem instantiated at the fitted box
predicts, for the assembled circuit: the DC output lies in the box output
interval, and the small-signal gain — measured exactly as in rung 1, a
central difference `ΔV_out/ΔV_in` for `ΔV_in = ±50 mV` around the bias —
lies in the corner interval (illustrative numbers above:
`[−22.4, −12.2]`).

**Falsification.** If the measured gain (or the measured DC output) lands
outside the predicted interval, the model-validity evidence is
**falsified** — say it exactly like that, loudly. What breaks is not any
theorem — the theorems are about the MOS1 model and remain true — but the
calibration hypothesis `haccepted`: the claim that this physical device is
covered by the MOS1 envelope on this domain at the fitted box. The
required response:

1. withdraw the `AcceptedValidity` value for the unit (it can no longer be
   constructed honestly);
2. record the falsifying measurement as a new `EvidenceRecord` whose
   `supersedes` points at the calibration record — the failure is
   provenance, not something to delete;
3. only then revise: refit the box, shrink the claimed domain, or extend
   the device model — and re-derive the interval from the corner lemmas.

No silent tolerance-widening: the interval was proved before the
measurement, and the measurement either lands in it or the envelope claim
dies. That asymmetry is the demo.
