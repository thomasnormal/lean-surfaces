# Circuit specification surface

**Status: normative design target with delivered vertical slices.** This is
the source/spec/proof gallery for the analysis-independent circuit
architecture. Some later sections intentionally show target syntax beyond
the implemented subset; the table below is the implementation ledger. The
exact divider, robust divider, hierarchy/contracts,
loaded-RC transient, vector RLC, loaded MOS inverter, exact AC and stability,
bounded noise/finite yield, thin and loaded DRAM cells, arbitrary-size bank,
the source-validated 2x2 DRAM endpoint contract, minimal Verilog-A, and sampled
mixed-signal slices are implemented. MOS
examples elaborate `.cir` source directly; Verilog-A uses the pinned OpenVAF
typed AST frontend. New work must either elaborate the relevant surface below
or deliberately revise this document in the same change.

The semantic root remains the acausal `Behavior` relation described in
`docs/circuit-assurance-architecture.md`. SPICE and Verilog-A are source
frontends; DC, transient, AC, noise, and yield are structured interpretations
of that relation. A numerical tool may validate an interpretation, but no
simulator result is a premise of a theorem.

| Design slice | Implementation |
|---|---|
| exact DC | `Examples/spice/typed_divider/` |
| robust PVT-style DC | `Examples/spice/robust_divider/` |
| exact hierarchy/contracts | `Examples/spice/chain/` |
| continuous RC + backward Euler | `Examples/spice/loaded_rc/` |
| vector RLC energy invariant | `Examples/spice/rlc_discharge/` |
| loaded MOS1 transient | `Examples/spice/loaded_inverter/` |
| thin 1T1C hold and write phases | `Examples/spice/dram_1t1c/` |
| loaded DRAM read + parametric bank | `Examples/spice/dram_bitcell/` |
| 2x2 DRAM endpoint contract | `Examples/spice/dram_bank_2x2/` |
| 256x32 DRAM endpoint contract | `Examples/spice/dram_bank_256x32/` |
| exact AC linearization | `Examples/spice/ac_lowpass/` |
| bounded noise + finite yield | `Examples/spice/robust_divider/` |
| MOS1 composition | `Examples/spice/{and_gate,half_adder,ripple_adder}/` |
| Verilog-A contribution subset | `Examples/verilog-a/resistor/` |
| SV/analog sampled connection | `Examples/mixed-signal/counter_connect/` |

The DRAM rows need precision about what is derived versus defined:
write-zero dynamics in `dram_1t1c` are derived from the MOS1 channel law.
Hold constancy is derived from the initial condition and the
absolutely-continuous zero-field DAE, so it is not a behavior conclusion;
inside the nonnegative rail domain the zero field is proved equal to the
cut-off bidirectional MOS1 access-device KCL field. Write-one uses a separate
physics-only program whose parameters are projected from the same open source
deck. Lean derives its complete piecewise MOS1/capacitor field, proves the
unique closed-form trajectory, and proves a source-backed `[3 V, 4 V]`
one-nanosecond guarantee from a discharged cell. Exact finite-time 4 V is not
claimed: the nominal static equations have a whole threshold-loss interval
of equilibria. The
`dram_bitcell` read slice's charge-sharing voltage, ideal sense stage, and
rail restore are definitional relations — only their sign/margin arithmetic
and the bank composition theorems are derived from them (see
`docs/spice-device-levels.md`). The `dram_bank_2x2` slice is a
source-validated compositional transient-endpoint prototype. It derives the
enabled MOS1/bitline-capacitor precharge trajectory and its 10 ns
`[2.47 V, 2.5 V]` endpoint, then propagates that interval through
charge-sharing and the static sense decision bands. It also derives
unselected-wordline zero-leakage hold preservation and device/KCL facts.
After sensing, every
selected-row cell follows a source-derived finite-horizon restore DAE while
its bitline remains clamped to the sense output. The same dimension-generic
proof gives read and write endpoints in `[0 V, 1 V]` for zero and
`[3 V, 4 V]` for one. The read equation manifest explicitly reports the
legacy two-inverter sense endpoint contract; the write program imports the
read endpoint phase. Its
two-inverter sense relation covers conservative low/high voltage bands, but
is not a regenerative differential margin, metastability, or sensing-time
theorem. It refines this contract to `DramBankStep`; continuous sense-phase
semantics must still connect the differential latch to the bank transaction.
The bank equations now derive a uniform `3/22 V` signed margin against an
otherwise precharged reference. `DramBankSenseBridge` proves, with fixed
physical line identities and paired residual realizability, that the nominal
four-MOS latch initially amplifies this sign at every address. This is a
composition theorem: the 2x2 deck still contains the two-inverter path and
does not instantiate the differential connection.
The `dram_sense_amp` slice is the source-backed physical successor: its
cross-coupled MOS1/capacitor DAE proves rail and midpoint equilibria are
inhabited. An exact derived scalar view is proved equivalent to the primitive
residual on the balanced manifold and lifts scalar physical trajectories
back into the vector DAE. For every `0 < deviation < 5/2`, the primitive
residual forces the selected node upward, its complement downward, and zero
common-mode derivative; a residual witness is provided for every such point.
For the first MOS region, the named exponential trace
`d(t) = d(0) * exp(10^9 t)` is proved absolutely continuous, proved to
satisfy the scalar DAE, lifted into the vector DAE, and packaged as an
inhabited equation-program behavior. Every scalar solution that remains in
that region is proved equal to this trace. The named primitive behavior stays
inside the supply rails and reaches a requested positive differential by
`max 0 (log(required / d(0)) / 10^9)`.
Its margin and resolution predicates live in a downstream spec module and
are explicitly forbidden dependencies of the equation program. A separate
Picard-Lindelof construction supplies a primitive trajectory across all three
MOS regions for every finite horizon and every initial deviation in
`[0, 5/2]`, with a proved rail-domain barrier. A global source-field
Lipschitz proof makes every balanced scalar AC trajectory with the same
initial deviation equal to that witness, so `NoOvershoot` holds without a
rail premise and regeneration is monotone throughout the finite horizon.
For the full source-derived two-node DAE, a KCL energy theorem proves that
every rail-valid vector trajectory with balanced initial data remains on the
balanced manifold. Such trajectories project exactly into the scalar view
and are determinate. For arbitrary common mode, a source-backed pointwise
theorem now proves that every ordered, nonterminal rail-valid state has a
strictly increasing voltage differential; a paired residual witness makes
the premise inhabited at every state. A globally Lipschitz proof extension
now constructs a nominal unbalanced primitive-DAE behavior for every finite
horizon; an inward-pointing barrier proves that witness stays in the rail
square, where the extension agrees exactly with the four source-derived MOS
currents. Unbalanced determinacy and convergence, mismatched-device and
offset margin, and quantitative rail-settling timing remain future theorem
shapes.
The `dram_bank_256x32` slice instantiates the generalized endpoint theorem;
its fail-closed source loader emits kernel-checked parameter and typed
cell/row/subarray/column/bank topology certificates for the embedded source.
Their composition proves the complete deck projection. Its generated columns
also contain a source-projected reference line, paired coupling gates, and
the four-MOS/two-capacitor latch. Lean proves pointwise residual realizability
and correct local regeneration from any `CouplingReady` state. A physical
finite-horizon transmission-gate trajectory now derives that state from the
bank's bitline/reference bounds after every positive coupling duration,
while proving pair-charge conservation, no overshoot, realizability, and
`[2 V, 3 V]` domain closure. That endpoint now initializes an inhabited
finite-horizon primitive latch behavior with proved 0--5 V domain closure.
Unbalanced determinacy, global convergence, and physical restore remain open,
so the generalized
endpoint theorem still reports the legacy sense endpoint contract as
imported. Scaling adds no per-cell proof cases.

## Surface contract

### Loading and checked names

```lean
load_circuit divider from "Examples/circuit/divider/divider.cir"
load_circuit limiter from "Examples/circuit/limiter/limiter.va"
```

`load_circuit` dispatches by source kind, retains source provenance, validates
the selected model profile, and creates a typed circuit literal. It may create
private elaboration companions for flattened hierarchy, equations, unknown
ordering, certificates, or model resolution. Those companions are plumbing:
ordinary statements do not mention them.

Every source-level object in a statement is checked during elaboration:

```lean
node! divider "out"
branch! rlc "l1"
port! limiter "in"
model! inverter "nmos"
```

Bare strings are not accepted where a node, branch, port, instance, or model
identifier is expected. A misspelling must fail at the statement, before a
proof tactic runs.

### Judgments

The braces bind readable accessors rather than exposing assignments, solver
vectors, flattened ASTs, or residual encodings.

| Surface | Meaning |
|---|---|
| `c ⊨dc { v, i => P }` | Every nominal DC behavior of `c` satisfies `P`. |
| `c ⊨dc[W] { w, v, i => P }` | Every DC behavior in every world allowed by `W` satisfies `P`. |
| `c ⊨tran[W] { w, tr => P }` | Every continuous behavior in `W` satisfies the trace property `P`. |
| `c ⊨ac[op, Ω] { ω, ac => P }` | Every small-signal behavior linearized at `op`, for `ω ∈ Ω`, satisfies `P`. |
| `RealizableDC c W` | Every world in `W` has at least one DC behavior. |
| `RealizableTransient c W` | Every world in `W` has at least one continuous behavior on its stated horizon. |

`OperatingPoint` contains a proved DC operating point and its validity
evidence. `FrequencySet` is a predicate, not necessarily a finite sweep.
`RealizableAC c op Ω` is the corresponding non-vacuity obligation for an AC
relation. It is included where AC is used, even though `RealizableDC` for the
linearization point is also required.

The primary proof front doors are:

* `circuit_dc`: exact or symbolic DC equations, including nonlinear case
  splits justified by the selected device model;
* `circuit_enclose`: interval, affine, polynomial, or measure bounds over a
  world set;
* `circuit_transient`: continuous DAE invariants, solution theorems, and
  separately stated numerical refinements; and
* `compose_contracts`: exact, over-approximate, or error-bounded composition,
  with the inclusion direction visible in the goal.

These tactics may use proved library lemmas. They do not add axioms, trust an
external solver, or silently turn an approximation into an exact view.

### Non-vacuity

Every universal behavior theorem is paired with realizability:

```lean
theorem block_safe : block ⊨dc[allowed] { w, v, i => property w v i } := by proofs
theorem block_realizable : RealizableDC block allowed := by proofs
theorem block_domain : StaysWithinDCValidity block allowed domain := by proofs

theorem block_assurance :
    AssuranceCase block behavior allowed property domain := by proofs

#assurance_report block using block_assurance []
```

`#circuit_check` is an executable, concrete smoke test:

```lean
#circuit_check block dc at nominalScenario shows v (node! block "out") = 1
```

It catches source, orientation, unit, and expected-value mistakes, but it does
not replace `RealizableDC` or `RealizableTransient`. A finite run cannot prove
that every allowed world has a behavior.

### Assurance reports

`#assurance_report circuit using assurance [supporting, ...]` is a checked
command, not prose generation. `assurance` must be an `AssuranceCase` attached
to that exact elaborated circuit. Its type binds safety, realizability, and
domain closure to the same behavior and allowed-world predicate; the optional
list carries determinacy, stability, coherence, numerical-refinement, and
physical-validity certificates. It must report:

* source kind, source hash, validated model profile, and checked hierarchy;
* semantic analysis and quantified world/frequency/horizon domain;
* exact, over-approximate, under-approximate, or error-bounded view direction;
* the universal theorem's paired realizability theorem;
* determinacy or well-posedness status for the observations used;
* model-validity domain and provenance, or an explicit missing-evidence item;
* arithmetic and automation used, including any numerical refinement theorem;
* theorem axioms; and
* external differential checks, labelled as validation rather than premises.

A report fails if the case belongs to a different circuit, depends on
nonstandard axioms, or lacks its structurally required safety, realizability,
or domain proof. View constructors reject an over-approximation used for a
witness and an under-approximation used for universal safety; claimed
validity/refinement edges require their own certificates.

Behavior definitions use provenance-carrying equation programs. Two commands
make that boundary visible and enforceable:

```lean
#equation_guard DramBankCoreReadProgram forbids
  [DramBankCoreReadSpecification, DramBankCoreWriteSpecification]

#equation_report dram_bank_256x32_read_equation_manifest
```

The guard rejects direct or transitive dependencies from the equation
program to either specification. The report prints the complete set of
imported contracts. The DRAM read program reports `[]`; its finite-horizon
restore endpoint is derived from the primitive DAE. The write program reports
only the preceding proved read phase.

## Gallery

The ten examples below are statement-level acceptance tests for the surface.
Each has source, spec, and proof. Ellipses occur only inside named scenario or
world-set records whose omitted fields are irrelevant to the statement; there
are no omitted theorem hypotheses.

### 1. Exact divider

Source:

```spice
* divider.cir
v1 in 0 dc 5
r1 in out 1k
r2 out 0 2k
.op
.end
```

Spec:

```lean
import Examples.circuit.divider.proof

open LeanModels.Circuit

load_circuit divider from "Examples/circuit/divider/divider.cir"

#circuit_check divider dc at .nominal
  shows v (node! divider "out") = (10 / 3 : Rat)

theorem divider_exact :
    divider ⊨dc { v, _i => v (node! divider "out") = 10 / 3 } := by proofs

theorem divider_realizable :
    RealizableDC divider (.nominal divider) := by proofs

theorem divider_wellposed :
    DeterminateDC divider (.nominal divider) := by proofs

#assurance_report divider using divider_assurance [divider_wellposed]
```

Proof:

```lean
namespace Examples.circuit.divider.proof

theorem divider_exact :
    divider ⊨dc { v, _i => v (node! divider "out") = 10 / 3 } := by
  circuit_dc

theorem divider_realizable :
    RealizableDC divider (.nominal divider) := by
  circuit_dc

theorem divider_wellposed :
    DeterminateDC divider (.nominal divider) := by
  circuit_dc

end Examples.circuit.divider.proof
```

This is exact rational MNA. The report must say that ngspice approximates the
proved `10/3`; it must not describe the floating-point comparison as evidence
used by `divider_exact`.

### 2. Robust divider

Source:

```spice
* robust_divider.cir
v1 in 0 dc 5
r1 in out 1k
r2 out 0 2k
.op
.end
```

Spec:

```lean
import Examples.circuit.robust_divider.proof

open LeanModels.Circuit

load_circuit robustDivider from
  "Examples/circuit/robust_divider/robust_divider.cir"

def dividerCorners : WorldSet robustDivider :=
  dcWorlds {
    supply := interval (19 / 4 : ℝ) (21 / 4)
    component "r1" := fixedPerInstance (interval 950 1050)
    component "r2" := fixedPerInstance (interval 1900 2100)
  }

#circuit_check robustDivider dc at dividerCorners.nominal
  shows v (node! robustDivider "out") = (10 / 3 : ℝ)

theorem robust_divider_safe :
    robustDivider ⊨dc[dividerCorners] { _w, v, _i =>
      361 / 118 ≤ v (node! robustDivider "out") ∧
      v (node! robustDivider "out") ≤ 441 / 122 } := by proofs

theorem robust_divider_realizable :
    RealizableDC robustDivider dividerCorners := by proofs

theorem robust_divider_domain :
    StaysWithinDCValidity robustDivider dividerCorners
      (voltageDomain 0 6) := by proofs

#assurance_report robustDivider using robust_divider_assurance []
```

Proof:

```lean
namespace Examples.circuit.robust_divider.proof

theorem robust_divider_safe :
    robustDivider ⊨dc[dividerCorners] { _w, v, _i =>
      361 / 118 ≤ v (node! robustDivider "out") ∧
      v (node! robustDivider "out") ≤ 441 / 122 } := by
  circuit_enclose

theorem robust_divider_realizable :
    RealizableDC robustDivider dividerCorners := by
  circuit_dc

theorem robust_divider_domain :
    StaysWithinDCValidity robustDivider dividerCorners
      (voltageDomain 0 6) := by
  circuit_enclose

end Examples.circuit.robust_divider.proof
```

`fixedPerInstance` is load-bearing: fabricated resistances do not change
adversarially between equations or time points. The interval is tight for the
declared independent box; a correlated process policy would be a different
`WorldSet`.

### 3. Hierarchical contract composition

Source:

```spice
* attenuator_chain.cir
.subckt attn a b
rseries a b 1k
rshunt b 0 6k
.ends attn

v1 in 0 dc 5
x1 in n1 attn
x2 n1 out attn
rterm out 0 3k
.op
.end
```

Spec:

```lean
import Examples.circuit.attenuator_chain.proof

open LeanModels.Circuit

load_circuit attenuatorDeck from
  "Examples/circuit/attenuator_chain/attenuator_chain.cir"

def attn := subcircuit! attenuatorDeck "attn"
def terminatedChain (n : Nat) := cascadeN n attn |>.terminate 3000

theorem section_contract :
    HasExactContract attn (twoPortY
      [[1 / 1000, -1 / 1000],
       [-1 / 1000, 7 / 6000]]) := by proofs

theorem chain_contract (n : Nat) :
    HasExactContract (terminatedChain n)
      (matchedAttenuatorContract n (2 / 3) 3000) := by proofs

theorem chain_realizable (n : Nat) :
    RealizableDC (terminatedChain n)
      (.nominal (terminatedChain n)) := by proofs

theorem chain_attenuates (n : Nat) :
    terminatedChain n ⊨dc { v, _i =>
      v (port! (terminatedChain n) "out") =
        (2 / 3 : Rat) ^ n * v (port! (terminatedChain n) "in") } := by proofs

#circuit_check (terminatedChain 5) dc
  at { drive (port! (terminatedChain 5) "in") := 5 }
  shows v (port! (terminatedChain 5) "out") = (2 / 3 : Rat) ^ 5 * 5

#assurance_report attenuatorDeck using chain_assurance [chain_contract]
```

Proof:

```lean
namespace Examples.circuit.attenuator_chain.proof

theorem section_contract :
    HasExactContract attn (twoPortY
      [[1 / 1000, -1 / 1000],
       [-1 / 1000, 7 / 6000]]) := by
  circuit_dc

theorem chain_contract (n : Nat) :
    HasExactContract (terminatedChain n)
      (matchedAttenuatorContract n (2 / 3) 3000) := by
  induction n with
  | zero => circuit_dc
  | succ n ih => compose_contracts [section_contract, ih]

theorem chain_realizable (n : Nat) :
    RealizableDC (terminatedChain n) (.nominal (terminatedChain n)) := by
  exact (chain_contract n).realizable

theorem chain_attenuates (n : Nat) :
    terminatedChain n ⊨dc { v, _i =>
      v (port! (terminatedChain n) "out") =
        (2 / 3 : Rat) ^ n * v (port! (terminatedChain n) "in") } := by
  exact (chain_contract n).safe

end Examples.circuit.attenuator_chain.proof
```

`HasExactContract` is a behavior equivalence, not projection-only soundness.
The reverse, realizability direction is what justifies the induction step.
The theorem quantifies over an unbounded circuit family without flattening
every member.

### 4. Loaded RC

Source:

```spice
* loaded_rc.cir
vstep in 0 dc 5
rdrive in out 1k
rload out 0 2k
cload out 0 1u
.tran 1u 10m
.end
```

Spec:

```lean
import Examples.circuit.loaded_rc.proof

open LeanModels.Circuit

load_circuit loadedRC from "Examples/circuit/loaded_rc/loaded_rc.cir"

def loadedRCRuns : WorldSet loadedRC :=
  transientWorlds {
    initial v (node! loadedRC "out") := 0
    horizon := 10 * millisecond
  }

#circuit_check loadedRC tran at loadedRCRuns.nominal
  time (10 * millisecond)
  shows v (node! loadedRC "out") ∈ interval 3.333332 3.333334

theorem loaded_rc_no_overshoot :
    loadedRC ⊨tran[loadedRCRuns] { _w, tr =>
      throughout tr fun _t =>
        0 ≤ tr.v (node! loadedRC "out") ∧
        tr.v (node! loadedRC "out") ≤ 10 / 3 } := by proofs

theorem loaded_rc_settles :
    loadedRC ⊨tran[loadedRCRuns] { _w, tr =>
      ∀ ε > 0, after (Real.log ((10 / 3) / ε) / 1500) tr fun _t =>
        |tr.v (node! loadedRC "out") - 10 / 3| ≤ ε } := by proofs

theorem loaded_rc_realizable :
    RealizableTransient loadedRC loadedRCRuns := by proofs

#assurance_report loadedRC using loaded_rc_assurance [loaded_rc_settles]
```

Proof:

```lean
namespace Examples.circuit.loaded_rc.proof

theorem loaded_rc_no_overshoot :
    loadedRC ⊨tran[loadedRCRuns] { _w, tr =>
      throughout tr fun _t =>
        0 ≤ tr.v (node! loadedRC "out") ∧
        tr.v (node! loadedRC "out") ≤ 10 / 3 } := by
  circuit_transient

theorem loaded_rc_settles :
    loadedRC ⊨tran[loadedRCRuns] { _w, tr =>
      ∀ ε > 0, after (Real.log ((10 / 3) / ε) / 1500) tr fun _t =>
        |tr.v (node! loadedRC "out") - 10 / 3| ≤ ε } := by
  circuit_transient

theorem loaded_rc_realizable :
    RealizableTransient loadedRC loadedRCRuns := by
  circuit_transient

end Examples.circuit.loaded_rc.proof
```

The judgment denotes the continuous DAE. A backward-Euler or ngspice trace
requires a separate refinement theorem and appears as such in the assurance
report; neither defines the physical behavior.

### 5. Multi-node RLC

Source:

```spice
* rlc_discharge.cir
cstore n1 0 1u ic=5
lpath n1 n2 1m ic=0
rload n2 0 10
csense n2 0 2u ic=0
.tran 100n 2m uic
.end
```

Spec:

```lean
import Examples.circuit.rlc_discharge.proof

open LeanModels.Circuit

load_circuit rlc from "Examples/circuit/rlc_discharge/rlc_discharge.cir"

def rlcRuns : WorldSet rlc :=
  transientWorlds {
    initial v (node! rlc "n1") := 5
    initial v (node! rlc "n2") := 0
    initial i (branch! rlc "lpath") := 0
    horizon := 2 * millisecond
  }

def storedEnergy (tr : CircuitTrace rlc) (t : ℝ) : ℝ :=
  (1 / 1000000) * (tr.vAt t (node! rlc "n1")) ^ 2 / 2 +
  (1 / 1000) * (tr.iAt t (branch! rlc "lpath")) ^ 2 / 2 +
  (2 / 1000000) * (tr.vAt t (node! rlc "n2")) ^ 2 / 2

#circuit_check rlc tran at rlcRuns.nominal time 0
  shows storedEnergy trace 0 = (1 / 80000 : ℝ)

theorem rlc_energy_dissipates :
    rlc ⊨tran[rlcRuns] { _w, tr =>
      ∀ t, 0 ≤ t → t ≤ tr.horizon → storedEnergy tr t ≤ storedEnergy tr 0 } :=
  by proofs

theorem rlc_realizable :
    RealizableTransient rlc rlcRuns := by proofs

theorem rlc_domain :
    StaysWithinTransientValidity rlc rlcRuns
      (voltageDomain (-5) 5 ×ˢ currentDomain (-1) 1) := by proofs

#assurance_report rlc using rlc_assurance []
```

Proof:

```lean
namespace Examples.circuit.rlc_discharge.proof

theorem rlc_energy_dissipates :
    rlc ⊨tran[rlcRuns] { _w, tr =>
      ∀ t, 0 ≤ t → t ≤ tr.horizon → storedEnergy tr t ≤ storedEnergy tr 0 } := by
  circuit_transient (storage := storedEnergy)

theorem rlc_realizable :
    RealizableTransient rlc rlcRuns := by
  circuit_transient

theorem rlc_domain :
    StaysWithinTransientValidity rlc rlcRuns
      (voltageDomain (-5) 5 ×ˢ currentDomain (-1) 1) := by
  circuit_transient (invariant := storedEnergy)

end Examples.circuit.rlc_discharge.proof
```

This acceptance test forces vector-valued DAEs and coupled state. The energy
derivative must reduce to `-10 * i(lpath)^2`; a scalar RC-only interpretation
cannot elaborate it.

### 6. MOS inverter

Source:

```spice
* mos_inverter.cir
.model ndev nmos level=1 vto=1 kp=100u lambda=0
.model pdev pmos level=1 vto=-1 kp=50u lambda=0
.subckt inv in out vdd vss
mp out in vdd vdd pdev
mn out in vss vss ndev
.ends inv
.end
```

Spec:

```lean
import Examples.circuit.mos_inverter.proof

open LeanModels.Circuit

load_circuit inverter from "Examples/circuit/mos_inverter/mos_inverter.cir"

def inverterCorners : WorldSet inverter :=
  dcWorlds {
    drive (port! inverter "vdd") := 5
    drive (port! inverter "vss") := 0
    drive (port! inverter "in") := logicRail 0 5
    require model! inverter "ndev" within mos1Validity
    require model! inverter "pdev" within mos1Validity
  }

#circuit_check inverter dc at (inverterCorners.withInput false)
  shows v (port! inverter "out") ≥ 4.5

theorem inverter_logic :
    inverter ⊨dc[inverterCorners] { w, v, _i =>
      logicValue 0.5 4.5 (v (port! inverter "out")) =
        some (!w.inputBit) } := by proofs

theorem inverter_realizable :
    RealizableDC inverter inverterCorners := by proofs

theorem inverter_model_domain :
    StaysWithinDCValidity inverter inverterCorners (voltageDomain 0 5) :=
  by proofs

#assurance_report inverter using inverter_assurance []
```

Proof:

```lean
namespace Examples.circuit.mos_inverter.proof

theorem inverter_logic :
    inverter ⊨dc[inverterCorners] { w, v, _i =>
      logicValue 0.5 4.5 (v (port! inverter "out")) =
        some (!w.inputBit) } := by
  circuit_dc

theorem inverter_realizable :
    RealizableDC inverter inverterCorners := by
  circuit_dc

theorem inverter_model_domain :
    StaysWithinDCValidity inverter inverterCorners (voltageDomain 0 5) := by
  circuit_enclose

end Examples.circuit.mos_inverter.proof
```

The report must identify the exact compact-model profile and the absent
refinement edges. This proves a theorem from MOS1 equations and KCL; it does
not claim BSIM, silicon, or Newton-iteration correctness.

The delivered dynamic inverter slice is
`Examples/spice/loaded_inverter/`. Its source is an open component containing
the complementary MOS pair and explicit output capacitor; supplies and input
drivers live in the run world. In addition to DC existence, it proves an
absolutely-continuous DAE behavior exists, every behavior remains within the
supply domain without overshoot, and the output error obeys an explicit
PVT-dependent exponential bound. The gallery surface above remains the
compact syntax target; the current checked statements use the underlying
`SafeUnder`, `RealizableUnder`, `NoOvershoot`, and `SettlesWithin` predicates
directly.

### 7. AC filter and amplifier

Source:

```spice
* active_lowpass.cir
vin in 0 dc 0 ac 1
r1 in mid 1k
c1 mid 0 1u
egain out 0 mid 0 10
.op
.ac lin 1 159.154943091895 159.154943091895
.end
```

Spec:

```lean
import Examples.circuit.active_lowpass.proof

open LeanModels.Circuit

load_circuit activeLP from
  "Examples/circuit/active_lowpass/active_lowpass.cir"

def activeLPOp : OperatingPoint activeLP := nominalOperatingPoint activeLP
def cutoff : FrequencySet := angularFrequencySingleton 1000

#circuit_check activeLP ac at activeLPOp frequency 1000
  shows gainSq (node! activeLP "out") (node! activeLP "in") = 50

theorem active_lp_cutoff :
    activeLP ⊨ac[activeLPOp, cutoff] { _ω, ac =>
      gainSq ac (node! activeLP "out") (node! activeLP "in") = 50 } :=
  by proofs

theorem active_lp_bias_realizable :
    RealizableDC activeLP activeLPOp.worlds := by proofs

theorem active_lp_ac_realizable :
    RealizableAC activeLP activeLPOp cutoff := by proofs

#assurance_report activeLP using active_lp_assurance []
```

Proof:

```lean
namespace Examples.circuit.active_lowpass.proof

theorem active_lp_cutoff :
    activeLP ⊨ac[activeLPOp, cutoff] { _ω, ac =>
      gainSq ac (node! activeLP "out") (node! activeLP "in") = 50 } := by
  circuit_enclose

theorem active_lp_bias_realizable :
    RealizableDC activeLP activeLPOp.worlds := by
  circuit_dc

theorem active_lp_ac_realizable :
    RealizableAC activeLP activeLPOp cutoff := by
  circuit_dc

end Examples.circuit.active_lowpass.proof
```

`gainSq` avoids a square root: at `ω = 1000 rad/s`, the tenfold amplifier
after the `1 kΩ, 1 uF` pole has magnitude squared `100 / 2 = 50`. The decimal
frequency on the source `.ac` card is only the ngspice validation request; the
typed theorem quantifies at exact angular frequency `1000`.

### 8. Noise and yield

Source:

```spice
* noisy_frontend.cir
vin in 0 dc 1 ac 1
rs in n 1k
rf out n 100k
eamp out 0 0 n 1meg
.noise v(out) vin dec 20 10 100k
.op
.end
```

Spec:

```lean
import Examples.circuit.noisy_frontend.proof

open LeanModels.Circuit

load_circuit frontend from
  "Examples/circuit/noisy_frontend/noisy_frontend.cir"

def frontendLot : MeasuredWorldSet frontend :=
  processMeasure {
    fixedPerInstance component "rs" ~ logNormal (1000) (0.01)
    fixedPerInstance component "rf" ~ logNormal (100000) (0.01)
    runNoise := thermalNoise (temperature := interval 290 310)
    correlation := independent ["rs", "rf"]
  }

#circuit_check frontend noise at frontendLot.nominal
  band 10 100000 shows outputRms < 2 * millivolt

theorem frontend_noise_safe :
    frontend ⊨dc[frontendLot.support] { _w, v, _i =>
      |v (node! frontend "out")| ≤ 102 } := by proofs

theorem frontend_yield :
    Yield frontendLot (fun w =>
      dcObservation frontend w (node! frontend "out") ∈ interval (-102) (-98) ∧
      outputNoiseRms frontend w (band 10 100000)
        (node! frontend "out") < 2 * millivolt)
      ≥ 0.997 := by proofs

theorem frontend_realizable :
    RealizableDC frontend frontendLot.support := by proofs

#assurance_report frontend using frontend_assurance [frontend_yield]
```

Proof:

```lean
namespace Examples.circuit.noisy_frontend.proof

theorem frontend_noise_safe :
    frontend ⊨dc[frontendLot.support] { _w, v, _i =>
      |v (node! frontend "out")| ≤ 102 } := by
  circuit_enclose

theorem frontend_yield :
    Yield frontendLot (fun w =>
      dcObservation frontend w (node! frontend "out") ∈ interval (-102) (-98) ∧
      outputNoiseRms frontend w (band 10 100000)
        (node! frontend "out") < 2 * millivolt)
      ≥ 0.997 := by
  circuit_enclose

theorem frontend_realizable :
    RealizableDC frontend frontendLot.support := by
  circuit_dc

end Examples.circuit.noisy_frontend.proof
```

The measure belongs to fabricated parameters; the run-noise process belongs
to each execution. `frontend_yield` is a theorem about the declared measure,
not Monte Carlo sample coverage. The report must expose distribution and
independence assumptions and distinguish the DC output-yield claim from the
separate integrated-noise check.

### 9. Verilog-A component

Source:

```verilog
// soft_limiter.va
`include "constants.vams"
`include "disciplines.vams"

module soft_limiter(in, out);
  input in;
  output out;
  electrical in, out;
  parameter real vmax = 1.0 from (0:inf);
  analog V(out) <+ vmax * tanh(V(in) / vmax);
endmodule
```

Spec:

```lean
import Examples.circuit.soft_limiter.proof

open LeanModels.Circuit

load_circuit limiter from
  "Examples/circuit/soft_limiter/soft_limiter.va"

def limiterInputs : WorldSet limiter :=
  dcWorlds { drive (port! limiter "in") := interval (-10) 10 }

#circuit_check limiter dc at { drive (port! limiter "in") := 0 }
  shows v (port! limiter "out") = 0

theorem limiter_transfer :
    limiter ⊨dc[limiterInputs] { _w, v, _i =>
      v (port! limiter "out") =
        Real.tanh (v (port! limiter "in")) } := by proofs

theorem limiter_bounded :
    limiter ⊨dc[limiterInputs] { _w, v, _i =>
      |v (port! limiter "out")| < 1 } := by proofs

theorem limiter_realizable :
    RealizableDC limiter limiterInputs := by proofs

#assurance_report limiter using limiter_assurance [limiter_bounded]
```

Proof:

```lean
namespace Examples.circuit.soft_limiter.proof

theorem limiter_transfer :
    limiter ⊨dc[limiterInputs] { _w, v, _i =>
      v (port! limiter "out") =
        Real.tanh (v (port! limiter "in")) } := by
  circuit_dc

theorem limiter_bounded :
    limiter ⊨dc[limiterInputs] { _w, v, _i =>
      |v (port! limiter "out")| < 1 } := by
  circuit_enclose

theorem limiter_realizable :
    RealizableDC limiter limiterInputs := by
  circuit_dc

end Examples.circuit.soft_limiter.proof
```

The frontend translates contribution statements into the same relational
behavior root as SPICE. Unsupported analog events, hidden state, discontinuous
operators, or discipline mismatches are retained and diagnosed; they are
never erased to make `circuit_dc` succeed.

### 10. DRAM bitcell

Source:

```spice
* dram_6t.cir
.model ndev nmos level=1 vto=0.45 kp=200u lambda=0
.model pdev pmos level=1 vto=-0.45 kp=100u lambda=0
.subckt bitcell q qb bl blb wl vdd vss
mpq q qb vdd vdd pdev
mnq q qb vss vss ndev
mpqb qb q vdd vdd pdev
mnqb qb q vss vss ndev
max q wl bl vss ndev
maxb qb wl blb vss ndev
.ends bitcell
.end
```

Spec:

```lean
import Examples.circuit.dram_6t.proof

open LeanModels.Circuit

load_circuit dramCell from "Examples/circuit/dram_6t/dram_6t.cir"

def readWorlds : WorldSet dramCell :=
  transientWorlds {
    drive (port! dramCell "vdd") := interval 0.95 1.05
    drive (port! dramCell "vss") := 0
    precharge (port! dramCell "bl") (port! dramCell "blb") := supply
    pulse (port! dramCell "wl") := readPulse (rise := 50 * picosecond)
    initialLogic (port! dramCell "q") (port! dramCell "qb") := eitherBit
    horizon := 2 * nanosecond
    require allModels within calibratedBitcellDomain
  }

#circuit_check dramCell tran at (readWorlds.nominal.withStoredBit true)
  time (2 * nanosecond) shows logicHigh (v (port! dramCell "q"))

theorem dram_read_nondestructive :
    dramCell ⊨tran[readWorlds] { w, tr =>
      throughout tr fun _t =>
        differentialLogic (tr.v (port! dramCell "q"))
          (tr.v (port! dramCell "qb")) = some w.storedBit } := by proofs

theorem dram_read_realizable :
    RealizableTransient dramCell readWorlds := by proofs

theorem dram_read_domain :
    StaysWithinTransientValidity dramCell readWorlds
      calibratedBitcellDomain := by proofs

#assurance_report dramCell using dram_read_assurance []
```

Proof:

```lean
namespace Examples.circuit.dram_6t.proof

theorem dram_read_nondestructive :
    dramCell ⊨tran[readWorlds] { w, tr =>
      throughout tr fun _t =>
        differentialLogic (tr.v (port! dramCell "q"))
          (tr.v (port! dramCell "qb")) = some w.storedBit } := by
  circuit_transient
    (invariant := bitcellReadInvariant)
    (contracts := [crossCoupledPair, accessPair, bitlineLoad])

theorem dram_read_realizable :
    RealizableTransient dramCell readWorlds := by
  compose_contracts [crossCoupledPair, accessPair, bitlineLoad]
  circuit_transient

theorem dram_read_domain :
    StaysWithinTransientValidity dramCell readWorlds
      calibratedBitcellDomain := by
  circuit_transient (invariant := bitcellReadInvariant)

end Examples.circuit.dram_6t.proof
```

The theorem is conditional on a named calibrated model domain, bitline load,
wordline slew, supply range, and finite horizon. A report with missing
calibration provenance is incomplete even when Lean proves the conditional
mathematics.

## Diagnostics

Diagnostics name the source object, analysis, and failed assurance obligation.
Representative messages are part of the surface contract:

```text
node!: `otu` is not a node of `divider`
  nearest checked node: `out`
  inspect with: #circuit_nodes divider
```

```text
circuit_enclose: cannot prove universal safety from `reducedModel`
  available view: UnderApproxView
  required direction: ExactView or OverApproxView
  an under-approximation may witness realizability, not cover all behavior
```

```text
#assurance_report: `frontend_assurance` is attached to a different elaborated circuit
  expected: frontend
  case circuit: calibrationFixture
```

```text
circuit_transient: model validity is not closed by the proposed invariant
  escaped quantity: V(q)
  required domain: [0 V, 1.05 V]
  remaining goal is displayed below
```

```text
load_circuit: unsupported Verilog-A operator `cross` at soft_limiter.va:18
  the operator was preserved in the source AST; no behavior was generated
```

Singular, inconsistent, or underconstrained circuits are not all called
"solver failure." Diagnostics distinguish no behavior, multiple observations,
an unconstrained internal variable, unsupported source semantics, and a
certificate reconstruction failure.

## Goal-state policy

Before explicit unfolding, goals and hypotheses print in surface form:

```lean
world : FrontendWorld
hworld : world ∈ frontendLot.support
hbehavior : frontend @dc world ⊨ behavior
⊢ |v(out)| ≤ 102
```

Checked identifiers print by their source names (`v(out)`, `i(lpath)`), with
instance paths when needed. World facts print as fabrication, environment,
noise, and discrepancy facts rather than projections from anonymous tuples.

`circuit_dc`, `circuit_enclose`, and `circuit_transient` expose named physical
residue when they stop:

```lean
h_r1 : i(r1) = (v(in) - v(out)) / R(r1)
h_r2 : i(r2) = v(out) / R(r2)
h_out_kcl : i(r1) = i(r2)
⊢ 361 / 118 ≤ v(out)
```

They do not dump JSON terms, flattened arrays, matrix row numbers, existential
assignment functions, or solver certificate internals. Those become visible
only after an explicit `unfold` of the relevant semantic layer or through a
dedicated inspection command such as `#circuit_equations`.

For composition, the goal must retain view direction:

```lean
hamp : ExactContract amplifier AmpC
hload : OverApproxContract load LoadC
⊢ OverApproxContract (amplifier ⋈ load) (AmpC ⋈ᶜ LoadC)
```

No delaborator may print an over-approximate or error-bounded contract as an
exact equality. This is an assurance property of the proof interface, not
cosmetic output formatting.
