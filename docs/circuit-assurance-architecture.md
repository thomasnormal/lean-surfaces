# Circuit assurance architecture

This document is the contract for analysis-independent analog assurance.
SPICE is one source frontend and one numerical comparison path; it is not the
identity of the semantic core.

## Semantic root

`LeanModels/Circuit/Behavior.lean` defines the root denotation as an acausal
relation between a run world, boundary behavior, and internal behavior. It
does not assume that a model is functional, deterministic, passive,
continuous, differentiable, realizable, or stable. Those are separate
properties proved under explicit domains and interface partitions.

The first implemented assurance obligations are:

* `SafeUnder`: every allowed behavior satisfies a property;
* `RealizableUnder`: every allowed world has at least one behavior;
* `ReceptiveUnder`: every allowed excitation under a selected interface view
  has an extension;
* `DeterminateUnder`: a selected observation is unique; and
* `StaysWithinValidityDomain`: every allowed behavior remains inside the
  domain on which its component models are justified.

Universal safety and realizability are deliberately separate. A safety
theorem over an empty behavior set is not a complete correctness result.
`AssuranceCase circuit behavior allowed specification domain` packages
safety, realizability, and domain closure only after their circuit, behavior,
and allowed-world parameters agree definitionally. `#assurance_report`
consumes this typed case rather than inferring non-vacuity from an arbitrary
list of theorem names, and rejects a case attached to a different source
circuit.

## Equation provenance and the specification boundary

Declarative behavior can smuggle a desired result into its premises unless
the equation/specification boundary is enforced. `Circuit.Equation` therefore
represents behavior as an `EquationProgram`: every clause carries exactly one
origin (`deviceLaw`, `connectionLaw`, `environment`, `initialCondition`,
`evolution`, or `importedContract`), and the behavior relation is generated
from all of those clauses.

Imported endpoint contracts are permitted during staged development, but
`EquationManifest` enumerates them completely and `#equation_report` exposes
them in proof output. `#equation_guard program forbids [specification]` scans
the program's transitive project dependencies and rejects a program that
calls a forbidden specification, even through a helper definition. CI
compiles an intentionally contaminated program and requires this rejection.

For the DRAM bank, `DramBankCore.lean` contains equations, manifests, and
realizability witnesses. `DramBankCoreSpec.lean` imports that core and
contains observation specifications, safety, domain closure, and digital
refinement. The reverse import is impossible. Current manifests state
that the read program imports no contracts, while the write phase imports
only the preceding proved read endpoint. Selected read restore and write
results are derived from source-backed finite-horizon trajectories:
`[0 V, 1 V]` for zero and `[3 V, 4 V]` for one after 1 ns. Unselected
wordline storage is derived from scalar 1T1C hold trajectories. During write,
other selected-row cells continue their sense-clamped restore trajectories.

## Worlds and uncertainty

`LeanModels/Circuit/World.lean` separates a fabricated instance from its
run-specific environment, noise realization, and model discrepancy.
Fabrication parameters are selected once per instance rather than
adversarially resampled at every time point.

Allowed worlds are arbitrary predicates. Independent tolerance boxes are one
possible policy; correlated process sets, spatial mismatch, slew-constrained
environments, causal discrepancy operators, and probability measures can be
added without changing the behavior denotation.

## Structured semantic views

Automation consumes structured views of the general relation. The logical
direction of each view is explicit:

* `ExactView` proves equality in both directions;
* `OverApproxView` covers every denotational behavior and is suitable for
  universal safety proofs; and
* `UnderApproxView` contains only genuine denotational behaviors and is
  suitable for realizability witnesses.

The contract layer already implements error-bounded scalar reductions with
explicit universal coverage and realizability directions. A future generic
`Behavior` view for arbitrary error relations must preserve the same
directionality. A solver-friendly approximation must never be used in the
wrong inclusion direction.

## Time and transient analysis

`LeanModels/Circuit/Time.lean` provides both dense traces and superdense
hybrid time. Continuous DAE capabilities use dense time today. The delivered
mixed-signal slice uses an ordered microstep at each physical sample time;
full event execution for future analog and digital event constructs remains a
separate semantic layer.

`LeanModels/Circuit/Transient.lean` defines scalar and vector DAE residuals.
The physical finite-horizon relation requires every state coordinate to be
absolutely continuous and requires one simultaneous derivative vector plus
the coupled residual almost everywhere. It therefore admits isolated
nondifferentiable switching instants without admitting jumps in stored state.
`SmoothBehavesOn` is a stronger proof capability and refines the physical
relation only with a separate absolute-continuity certificate. Equilibrium is
a zero-derivative residual. Backward Euler remains a separate numerical
relation over the same residual and does not define the physical semantics.

## Validation slice 1: robust DC divider

`Examples/spice/robust_divider/` contains a literal SPICE divider and its
three-file code/spec/proof presentation.

The direct Lean frontend checks topology, orientations, element kinds,
ground connection, and nominal values while constructing the shared typed
circuit. The robust real-valued model then quantifies over fabricated
resistance values and run-specific supply voltage.

The example proves separately:

* nominal exact-DC non-vacuity through the rational SPICE solver;
* robust realizability at every allowed corner;
* output determinacy;
* the tight bound
  `361/118 <= Vout <= 441/122` for +/-5% source and resistor variation; and
* invariance of a 0--6 V model-validity domain.

The physical relation contains the source law, two instances of Ohm's law,
and output-node KCL. The closed-form divider equation is derived rather than
assumed. `Circuit.Enclosure` then computes the tight rational-endpoint range
and applies a generic, kernel-checked monotonicity certificate through
`circuit_enclose`; no sampled corner or floating-point interval is a proof
premise.

## Validation slice 2: loaded RC network

`Examples/spice/loaded_rc/` contains a source, series resistor, load
resistor, and output capacitor. A checked `ElaboratedCircuit` capability
recognizes this topology before exact source literals are embedded into the
real-valued transient interpretation.

The continuous residual is:

```text
C * dVout/dt + (Vout - Vs)/Rseries + Vout/Rload = 0.
```

For the extracted values, the DC target is exactly `10/3` V and the decay
rate is exactly `1500 s^-1`. The proof:

* exhibits the exponential trace and checks its derivative and DAE residual;
* proves finite-horizon realizability;
* proves uniqueness for all absolutely-continuous solutions by an
  integrating factor whose derivative is zero almost everywhere;
* proves monotone settling, nonnegativity, and no overshoot for every DAE
  behavior;
* proves validity-domain invariance;
* proves the explicit deadline
  `log(initial_error / epsilon) / rate`; and
* proves that every positive-step backward-Euler trajectory satisfies the
  numerical residual and cannot overshoot, with no timestep upper bound.

The ngspice and Spectre transient harnesses are differential validation.
They compare independent adaptive floating-point traces against the analytic
trace proved in Lean; neither simulator is a premise of the theorem.

## Validation slice 3: hierarchy and exact contracts

The direct Lean SPICE frontend retains `.SUBCKT` definitions and `X`
instances before elaborating a checked flattened DC circuit. `subcircuit!`
selects a source block only after its name and electrical ports have been
checked.

`Examples/spice/chain/` proves the exact two-port admittance relation of one
resistive attenuator in both directions: every implementation behavior
projects to the contract, and every boundary point satisfying the contract
has an implementation behavior. The generic `compose_contracts` theorem
eliminates a shared port without reopening either implementation.
`chain_contract` then uses the section theorem inductively to prove exact
`(2/3)^N` attenuation for every cascade length.

The same slice also distinguishes reduced contracts from exact ones.
`HasErrorBoundedContract` carries universal error coverage and separate
input-relative realizability. `compose_error_bounded_contracts` proves that
serial errors accumulate as `|downstream gain| * upstream error + downstream
error`; the chain example computes two `2/3 +/- 1/100` blocks to an exact
composite budget of `1/60` without claiming the envelope itself is exact.

## Validation slice 4: vector DAE and RLC energy

`LeanModels/Circuit/Transient.lean` also defines vector state, trace,
absolutely-continuous almost-everywhere DAE, equilibrium, and backward-Euler
relations. The continuous relation remains separate from numerical
execution.

`Examples/spice/rlc_discharge/` checks a capacitor-inductor-resistor topology
from source and interprets it as a two-state DAE. It exhibits the exact
critically damped trajectory, proving realizability from the required initial
condition. For every admitted absolutely-continuous behavior, the derivative
of stored capacitor-plus-inductor energy is `-R*i^2` almost everywhere.
The fundamental theorem for absolutely-continuous functions then proves that
energy never increases and the energy validity domain is invariant. This
theorem permits physically valid node-voltage ringing while bounding the
total transient.

## Validation slice 5: exact small-signal AC

`LeanModels/Circuit/AC.lean` defines exact Gaussian rationals and a structured
linear frequency-domain view. `ExactLinearizationAt` is an operating-point
capability, not a global assumption about every component.

`Examples/spice/ac_lowpass/` proves that the AC residual is exactly the
linearization of the loaded-RC transient residual at its DC operating point.
At `1500 rad/s`, a unit input has output exactly `1/3 - j/3` and squared
magnitude `2/9`. Realizability and output determinacy are separate theorems.
Both ngspice and Spectre are checked against this exact result.

## Validation slice 6: charge-consistent loaded MOS inverter

`Examples/spice/loaded_inverter/` is an open PMOS/NMOS component with an
explicit output capacitor. Supplies and input drivers are selected by the run
world and appear only in simulator testbenches; they are not fixed devices
inside the proved component. The checked source adapter requires exactly one
PMOS, one NMOS, one output-to-ground capacitor, the expected shared typed
nodes, and the named `LEVEL=1`, `LAMBDA=0`, `IS=0` model profile.

The MOS1 profile has no intrinsic charge model, so its intrinsic terminal
charge is explicitly zero. The load capacitor contributes equal-and-opposite
terminal charge. Its scalar DAE balances the derivative of that stored charge
against the MOS rail current. The public behavior bundles the
absolutely-continuous, almost-everywhere DAE denotation with the proved smooth
capability used for quantitative settling.

For every correlated fabrication corner and allowed run environment, Lean
proves:

* a nonlinear DC operating point exists by the intermediate value theorem;
* a finite-horizon transient exists by Picard-Lindelof;
* every admitted transient stays between ground and supply and cannot
  overshoot;
* the trajectory remains inside the compact-model validity domain;
* output error is bounded by an instance-specific exponential envelope;
* any deadline whose envelope is below a chosen tolerance satisfies
  `SettlesWithin`; and
* rail-valued DC operation draws zero channel current in the named ideal
  profile.

Ngspice and Spectre independently exercise rising and falling temporary
testbenches. Both comparison paths check boundedness, monotonicity, and the
quantitative envelope, but neither simulator is a premise of the theorems.
The assurance report intentionally records that physical coverage evidence
for fabricated devices is still missing.

## Validation slice 7: thin open 1T1C DRAM cell

`Examples/spice/dram_1t1c/` contains one NMOS access device and one 30 fF
storage capacitor. The reusable deck has no wordline or bitline sources.
Its checked adapter resolves the storage, wordline, and bitline nodes and
requires the named NMOS model profile.

This deliberately thin slice separates device-derived operations from the
one remaining idealized mode:

* write-zero is derived from the device law: with the wordline high and
  bitline at ground, the write-zero DAE field is proved equal to the
  normalized MOS1 channel current divided by the extracted capacitance
  (`dram1T1C_writeField_eq_mos1`). A behavior exists, remains between ground
  and supply without overshoot, and satisfies the inherited exponential
  settling deadline — all through the loaded-inverter MOS1 analysis;
* write-one is a separate source-backed `DramWriteBehavior`. The checked
  adapter projects threshold, transconductance, and storage capacitance from
  the open cell deck. Primitive bidirectional MOS1 current plus capacitor KCL
  reduces to a proved piecewise field, whose closed-form trajectory is proved
  to be the unique absolutely-continuous behavior from its initial voltage.
  Every admitted trajectory stays below the threshold-loss target and,
  from 0 V, enters `[3 V, 4 V]` within 1 ns. Safety, realizability, and rail
  closure are reported together; and
* hold constancy is derived from the initial condition and the
  absolutely-continuous DAE: the hold-mode residual forces zero derivative,
  and a reusable calculus theorem proves every physical trace constant. The
  equation manifest is empty. The hold field is still *defined* to be zero;
  MOS1 cutoff with `IS=0` is the recorded modeling rationale, but no MOS
  current or wordline voltage is yet consulted in that branch.

The write-one theorem intentionally does not claim an exact finite-time
4 V endpoint. For the nominal unboosted LEVEL=1 model, every storage voltage
between `VWL - Vt` and the 5 V bitline is a zero-current equilibrium; Lean
exhibits 4 V and 5 V as distinct equilibria. The transient and its deadline,
not the static equilibrium relation, select the useful write band. Read charge
sharing and nonzero-leakage retention remain outside this thin slice. Ngspice
and Spectre validate hold, write-zero, and write-one in temporary testbenches
only.

## Validation slice 8: bounded noise and finite yield

`Circuit.NoiseYield` keeps adversarial noise separate from probability.
The robust divider proves that bounded additive observation noise widens its
already-proved electrical interval by exactly the admitted radius.

`FiniteDistribution` selects whole correlated worlds with exact real
weights. `FiniteAlmostSure.yield_eq_one` proves a numeric probability-one
result only after every positive-weight world has the circuit property.
This does not turn a finite validation dataset into physical coverage
evidence.

## Validation slice 9: loaded DRAM read and arbitrary-size bank

`Examples/spice/dram_bitcell/` adds an explicit bitline capacitance to the
typed 1T1C component. This read slice is spec-level, not device-derived: the
charge-sharing shared voltage is a *definition* (`dramSharedVoltage`, the
standard charge-conservation formula), and `DramReadBehavior` definitionally
asserts that formula together with an ideal relational sense stage and a
restore that writes back the sensed rail. The access transistor's MOS1 law is
never consulted by the read relation; its extracted parameters are checked by
the topology adapter only. What *is* derived is arithmetic over that
definitional relation: the sign of the sense signal, the exact nominal
`5/22 V` margin, and read correctness/nondestructiveness given the ideal
sense component. The proved `nominalRead` parameters are hand-written scaled
values whose ratio matches the extracted deck capacitances; no theorem links
them to the extracted farad values.

The sense/restore relation is an explicit ideal component capability. Its
future transistor-level refinement is visible rather than silently assumed.
The cell contract composes into read and write refinement theorems for every
bank width; the bank write relation is itself definitional
(`Function.update`) and mentions no circuit at all.

## Validation slice 10: source-validated 2x2 endpoint-contract prototype

`Examples/spice/dram_bank_2x2/` is an open component deck with four physical
1T1C cells, shared wordlines and bitlines, a transistor-level row decoder,
precharge devices, one two-inverter sense path and restore transmission gate
per column, a post-sense read mux, and a column-selected write path. Supplies,
address rails, complementary controls, data input, initial charge, and phase
timing are testbench concerns and do not appear as fixed sources in the
proved component.

The strict source adapter checks all 46 flattened devices, all capacitor
values, every terminal and boundary node, and the three MOS1 model profiles
before returning `DramBank2x2Layout`. The physical semantics uses
source/drain-symmetric terminal current, because access-transistor charge
sharing reverses current direction according to the stored value.

The proof is compositional, but its boundary is deliberately narrow:

* one 1T1C endpoint contract derives charge conservation and access-device
  equilibrium from the extracted capacitances and MOS1 parameters;
* row activation composes that cell theorem across both columns;
* transistor equations characterize decoder, transmission gates, the
  two-inverter nominal sense path, and read muxing;
* the precharged bitline is the 10 ns endpoint of the enabled MOS1 plus
  300 fF bitline-capacitor DAE; Lean proves its unique trace stays below
  `5/2 V` and reaches at least `2.47 V`, rather than importing an equilibrium;
* every cell on an unselected wordline carries a source-parameterized 1T1C
  hold trace whose initial condition and zero-leakage DAE derive preservation
  at the connected phase endpoint;
* every selected-row cell follows a finite-horizon source-backed restore
  trajectory with its bitline clamped to the sense output;
* during a column write, other selected-row cells continue those clamped
  restore trajectories while unselected rows remain in cutoff hold; and
* the resulting read and write endpoints place zero in `[0 V, 1 V]` and one
  in `[3 V, 4 V]`.

For both read and write, Lean proves universal safety, realizability, and
0--5 V validity-domain closure. The read equation manifest explicitly records
the legacy two-inverter sense endpoint contract; the write theorem consumes
the read endpoint phase and then derives its selected and unselected-column
trajectories. Separate
refinement theorems connect its observations to `DramBankStep`. These are
non-vacuous theorems. Precharge timing is now a physical trajectory result;
the remaining timing gap is the connection from charge sharing into the
regenerative differential sense phase.

The current sense path is two cascaded inverters. Its discrimination lemmas
cover conservative low/high shared-voltage bands. The relation is still
single-ended and static, and admits a non-rail solution at its switching
boundary. No bank-level regenerative-latch, offset, resolution-time, or
metastability-exclusion theorem is claimed. The source-derived precharge and
charge-sharing phases do prove a uniform `3/22 V` differential relative to
an otherwise precharged reference. A separate contract bridge preserves
fixed `BL` and `BLref` identities and proves the nominal latch's local
regenerative direction for both bit polarities, together with pointwise
residual realizability. The 2x2 deck does not instantiate that connection.

`Examples/spice/dram_sense_amp/` now supplies the next source-backed vertical
slice: a cross-coupled differential latch with two explicit capacitors. Its
equation manifest contains only initial conditions and the primitive
capacitor/MOS1 KCL evolution. The kernel proves source projection, both rail
equilibria, and a realizable midpoint metastable equilibrium. It also proves
an exact scalar differential-mode reduction of the primitive residual,
physical-trajectory lifting, local residual realizability, and regenerative
direction throughout the balanced interval between midpoint and rail. The
first operating region additionally has an exact exponential,
absolutely-continuous behavior witness lifted all the way into the equation
program. An integrating-factor proof makes that scalar trajectory unique
among first-region solutions. The exhibited primitive behavior has a proved
rail-domain bound and reaches any requested positive first-region margin by
an explicit logarithmic deadline. The separate specification module defines
margin and resolution predicates, and the equation dependency guard proves
the DAE does not depend on either. Picard-Lindelof now constructs an
absolutely-continuous primitive trajectory across all three MOS regions for
every finite horizon and every initial balanced deviation in `[0, 5/2]`.
A source-derived barrier proves that witness stays in the rail domain. A
global five-region source field, bounded-image Lipschitz certificate, and
Grönwall argument prove finite-horizon determinacy without a rail premise.
Consequently every admissible balanced scalar trajectory remains in the
basin and moves monotonically toward the selected rail. At the primitive
two-node level, the MOS/KCL equations make squared common-mode error
nonincreasing inside the rail rectangle. Therefore every rail-valid vector
trajectory with balanced initial data stays balanced, projects into the
exact scalar view, and is determinate. For arbitrary nominal unbalanced
initial data, a globally Lipschitz clamped field now constructs an inhabited
finite-horizon primitive DAE behavior; a source-field barrier keeps that
witness in the rail rectangle, so the extension agrees with the primitive
MOS/KCL equations throughout. Determinacy of every arbitrary unbalanced
vector behavior is still open. At the local level,
however, a source-backed device-order theorem proves that every ordered,
nonterminal state anywhere in the rail rectangle has a strictly growing
voltage differential. Positive source-projected capacitances construct a
residual witness at every state. Unbalanced determinacy and convergence,
mismatched-device and offset coverage, and quantitative rail settling remain
intentionally open.

This slice does not derive a single continuous trajectory across every bank
phase or a
`DramBankTransactionContract` deadline. Ngspice and Spectre independently
validate precharge, charge-sharing targets, sensing, restoration, and writes.
The harness deliberately requires restoration to finish before write; a
shorter restore window exposed incomplete recovery of the other selected-row
cell. Simulator timing is evidence, not a theorem premise. The zero-leakage
MOS1 profile does not establish physical retention, refresh, or stressed-PVT
coverage.

## Validation slice 10a: generalized 256x32 DRAM bank

`Examples/spice/dram_bank_256x32/` scales the endpoint-contract argument
without scaling the proof by the number of cells. A reusable 32-cell row is
instantiated 256 times in the concrete open `.cir` component. The fail-closed
loader validates all row instances, bitline capacitances, per-column paths,
and model profiles. Separate kernel-checked certificates derive every numeric
field and the typed cell/row/subarray/column/bank topology from the embedded
source, then prove the complete `SourceCircuit.toDramBank` projection.

The endpoint-contract theorem quantifies over arbitrary `rows` and `columns`.
Instantiating it proves all-address read and write safety, realizability,
0--5 V domain closure, and refinement to `DramBankStep` for 8,192 cells,
relative to an explicitly reported legacy two-inverter sense endpoint
contract. The read restore and selected write phases have the same derived
1 ns logic-band guarantee as the 2x2 bank.

The generated 256x32 source now goes beyond that endpoint theorem: every
column contains a precharged reference bitline, paired transmission-gate
couplers, and an isolated four-MOS/two-capacitor differential latch with
separate sense rails. The strict source projection checks that connection and
derives the latch thresholds, transconductance, and capacitances. A
source-instance theorem proves the primitive latch residual is realizable and
that every rail-valid, correctly ordered nonterminal post-coupling state has
the correct regenerative derivative. A source-derived finite coupling
trajectory now establishes that state from the already-derived `3/22 V`
bitline/reference margin after every positive coupling duration. The proof
uses the four capacitor-KCL/MOS1 equations, proves pair-charge conservation,
no overshoot, finite-horizon realizability, and `[2 V, 3 V]` domain closure,
then derives the latch's correct initial regenerative direction. The
coupling endpoint now initializes an inhabited finite-horizon primitive latch
behavior whose two nodes are proved to remain in the 0--5 V model domain. The
missing refinement is determinacy and convergence of that unbalanced latch
behavior followed by physical restore. Until those land, the whole-bank
endpoint theorem retains the imported legacy sense contract and does not
claim a continuous transaction deadline. Ngspice and Spectre separately
exercise both read and write polarities through the 16,000-plus-device
hierarchy.

## Validation slice 11: frontend-independent sampled refinement

`Circuit.MixedSignal` uses superdense sample times, voltage bands, and
explicit logic/electrical connect relations. `MixedRuns` embeds the existing
SystemVerilog `Runs` judgment, including its quantified legal schedule
oracle. The composition theorem transports any proved SV trace property and
the sampled analog connection relation without defining a second scheduler.

This relation is not a Verilog-AMS frontend or execution semantics. OpenVAF
owns the active Verilog-A subset. Full mixed Verilog-AMS support is deferred
in `docs/backlog.md` and will require a suitable pinned third-party AST
frontend.

## Source and validation boundary

`load_circuit` parses the supported linear and MOS SPICE subset directly in
Lean, retains source text and a hash, and elaborates one analysis-neutral
`ElaboratedCircuit`. Exact linear DC and restricted MOS1 are fallible,
proof-carrying projections of that artifact. The legacy SPICE AST, JSON
ingester, solver, switch semantics, and dual public API have been removed.

Verilog-A deliberately uses a different frontend boundary. OpenVAF Reloaded's
typed syntax tree, pinned to revision
`b4517adc0a21ef42e03b396373553a41174444c4`, performs preprocessing and parsing.
`extractors/veriloga/extract.py` projects that tree into a deterministic JSON
envelope while preserving exact numeric token text. `load_veriloga` checks
that the envelope embeds the current `.va` source byte-for-byte, decodes the
projection, and resolves every port and parameter to typed Lean IDs. OpenVAF
is therefore the untrusted source frontend, not a theorem oracle. The initial
subset covers conservative electrical `inout` ports, exact real parameter
defaults, additive `V`/`I` contributions, arithmetic, and `ddt(V(...))`.
Every other parsed construct is rejected explicitly.

ngspice is available in ordinary CI. Cadence Spectre is proprietary, so it
runs conditionally on licensed hosts. The Spectre harness covers exact DC,
loaded-RC, RLC, and loaded-inverter transient behavior, exact AC, the complete
AND/half-adder truth tables, and four 50-bit ripple-adder vectors. Agreement is
recorded as validation evidence; it never becomes a theorem premise.

## Current boundary

The implemented slices validate typed electrical natures and conservative
disciplines, relational behavior, structured worlds, semantic-view inclusion
directions, non-vacuity, determinacy, domain closure, exact DC, exact
hierarchical contracts, scalar and vector continuous DAEs, settling and
energy bounds, separate backward-Euler semantics, operating-point
linearization, exact small-signal AC, provenance records, checked assurance
reports, and an OpenVAF-backed minimal Verilog-A contribution frontend.
It also includes deterministic bounded-noise propagation, exact finite
whole-world yield, spec-level charge-sharing DRAM read/restore contracts
composed for arbitrary bank widths (definitional relations; see slice 9), a
source-validated 2x2 bank endpoint contract with read/write refinement
(see slice 10), and sampled analog/SV refinement over the existing
all-schedule SV semantics.
The loaded-inverter slice additionally validates charge accounting,
nonlinear real DC existence, correlated PVT worlds, finite-horizon nonlinear
transient existence, no-overshoot/domain invariance, and an exponential
settling bound.
The thin 1T1C slice then demonstrates source-backed dynamic storage,
environment-controlled access, exact zero-leakage retention (derived from
the hold DAE and its initial condition; the zero field is the ideal compact
model choice), MOS1-derived write-zero, and a source-projected write-one
trajectory with determinacy and a one-nanosecond logic-band guarantee, all
without embedding testbench drivers.

The following architecture pieces remain to be implemented or generalized:

* source-level elaboration and automatic insertion of general signal-flow
  resolution and connect modules beyond the delivered rail-sampling relation;
* hybrid/event execution behavior over the already defined superdense
  timeline and typed event-lowering target;
* reusable correlated-process and stochastic-process libraries beyond the
  delivered whole-world finite distribution and bounded-noise theorems;
* accepted physical-validity certificates for the example model envelopes;
* error-bounded model reduction and continuous/numerical refinement;
* spectral/stochastic noise processes, general statistical yield, and
  electrothermal interpretations; and
* the remaining Verilog-A language.

Full Verilog-AMS is a separate deferred project; its parser, elaboration,
hybrid scheduling, and proof gates are recorded in `docs/backlog.md`.

### Known gaps (audited 2026-07-25)

* Semantic adapters remain proof-relevant code. `SourceBinding` closes the
  former phantom-circuit hole by requiring the exact checked projection and
  by making both behavior and allowed worlds definitionally arise from its
  projected model. Lean cannot infer the informal fact that an arbitrary
  adapter function uses every model field. Each source adapter therefore
  needs a strict projection theorem and an audit of the resulting semantics.
  The 2x2 bank adapter enumerates every device and model and its assurance
  cases consume the resulting typed layout; a user-written projection that
  simply returns an unrelated model would remain an explicit, reviewable
  trusted definition rather than a hidden theorem premise.
* Elaboration-time dimension checking. `Nature.lean` declares SI dimensions,
  natures, and conservative/signal disciplines, but that machinery is not
  wired into any elaboration path: dimensionally invalid values currently
  elaborate without complaint. Implementation queued.

Physical applicability remains conditional on evidence that the selected
component envelope covers fabricated devices throughout the proved invariant
domain. Lean proves the circuit theorem from that envelope; it does not turn
measurements or a PDK declaration into a kernel theorem automatically.
