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
full event execution for lowered Verilog-AMS `cross`, `timer`, and digital
events remains a separate semantic layer.

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

This deliberately thin slice proves two operations from the actual access
MOS current:

* with the wordline low, MOS1 cutoff and `IS=0` make the capacitor charge and
  storage voltage exactly constant for the full finite horizon; and
* with the wordline high and bitline at ground, the write-zero DAE is exactly
  the normalized MOS1 channel current divided by the extracted capacitance.
  A behavior exists, remains between ground and supply without overshoot, and
  satisfies the inherited exponential settling deadline.

The slice does not idealize unsupported operations. Ngspice and Spectre
validate hold and write-zero in temporary testbenches only.

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
typed 1T1C component. Charge conservation derives the shared voltage and
proves an exact nominal `5/22 V` sense margin. Reads are realizable,
nondestructive at the digital contract, and restore the stored rail.

The sense/restore relation is an explicit ideal component capability. Its
future transistor-level refinement is visible rather than silently assumed.
The cell contract composes into read and write refinement theorems for every
bank width.

## Validation slice 10: mixed-signal sampled refinement

`Circuit.MixedSignal` uses superdense sample times, voltage bands, and
explicit logic/electrical connect relations. `MixedRuns` embeds the existing
SystemVerilog `Runs` judgment, including its quantified legal schedule
oracle. The composition theorem transports any proved SV trace property and
the sampled analog connection relation without defining a second scheduler.

`VerilogAMS.Ast` is a typed lowering target for disciplines, connect modules,
and events. It is intentionally not a handwritten source parser. OpenVAF
continues to own the Verilog-A subset; source-level mixed Verilog-AMS waits
for a suitable pinned third-party AST frontend.

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
whole-world yield, charge-sharing DRAM read/restore contracts composed for
arbitrary bank widths, and sampled analog/SV refinement over the existing
all-schedule SV semantics.
The loaded-inverter slice additionally validates charge accounting,
nonlinear real DC existence, correlated PVT worlds, finite-horizon nonlinear
transient existence, no-overshoot/domain invariance, and an exponential
settling bound.
The thin 1T1C slice then demonstrates source-backed dynamic storage,
environment-controlled access, exact zero-leakage retention, and a
MOS1-derived write operation without embedding testbench drivers.

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
* the remaining Verilog-A language plus a source-level mixed-signal
  Verilog-AMS frontend backed by a suitable pinned third-party AST.

Physical applicability remains conditional on evidence that the selected
component envelope covers fabricated devices throughout the proved invariant
domain. Lean proves the circuit theorem from that envelope; it does not turn
measurements or a PDK declaration into a kernel theorem automatically.
