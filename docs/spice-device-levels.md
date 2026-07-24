# SPICE device-model levels and assurance boundary

The formal stack distinguishes equations from refinements. Defining two model
levels does not justify replacing one with the other. A vertical correctness
claim requires an `ExactRefinement` proof, or a
`BoundedObservableRefinement` plus a robustness theorem showing that its error
cannot cross a logic threshold.

## Specified levels

| Level | Lean specification | State |
|---|---|---|
| Quantum transport | `QuantumTransportSpec` | finite-basis retarded/lesser Green functions satisfying Dyson and Keldysh equations |
| Semiclassical transport | `BoltzmannTransportSpec` | steady one-dimensional phase-space distribution with collision operator and inflow contacts |
| Drift-diffusion | `DriftDiffusionSpec` | Poisson, electron/hole current laws, continuity, and contact boundary conditions |
| Compact transistor | `Mos1ChannelSpec`, `Mos1Satisfies` | ngspice Level-1 square-law channel current, voltage-source laws, and circuit KCL |
| Static CMOS logic | `Mos1AndEquations`, `Mos1OrEquations`, `Mos1InverterEquations` | bounded internal node voltages and local KCL |
| Arithmetic blocks | `Mos1HalfAdderContract`, `RippleAdderOf` | rail-valued half-adder observations and width-parametric composition |

The transport specifications deliberately contain no existence, uniqueness,
discretization, or solver claims.

## Proved vertical segment

The checked segment currently starts at a restricted MOS1 DC model:

```text
extracted .model parameters and MOS cards
  -> MOS1 channel equation + voltage-source laws + KCL
  -> CMOS inverter / AND / OR rail behavior
  -> extracted 20-transistor half-adder
  -> three-half-adder full-adder relation
  -> N-bit ripple arithmetic, for every N
```

The top theorem is compositional rather than a single 240-transistor
elimination. `half_adder_mos1_correct` proves the extracted reusable block
once. `ripple_adder_mos1_correct` then proves that, for every width, a
`RippleAdderOf` network whose component observations satisfy that physical
contract implements unsigned addition. Its premise contains the local MOS1
states, KCL, supply envelope, rail-valued wiring observations, and shared
Boolean port values. No ideal-switch premise occurs in this chain.

The committed four-bit deck is an executable realization of that structure,
checked at several vectors by ngspice. A further theorem projecting every
satisfying state of the single flattened 240-transistor deck into the local
`RippleAdderOf` observations remains open. Until that wiring/refinement
theorem lands, the correct claim is compositional MOS1 soundness plus an
ngspice realization check, not monolithic formal verification of the deck.

The deck profile is explicit: `LEVEL=1`, `VTO=1/-1`, positive `KP`,
`LAMBDA=0`, `IS=0`, omitted device dimensions (`W/L=1`), steady DC, no gate
or body current, source-oriented channels, and all observed nodes within the
0--5 V supply envelope. `Netlist.toMos1` rejects a deck that does not provide
this profile. Successful validation produces a `Mos1Circuit`: node, voltage
source, transistor, and model identifiers have distinct Lean types; every
transistor contains its resolved `Mos1Model`; and the required parameters are
named structure fields rather than a string-keyed array. The logic theorems
are soundness results: any satisfying state in the envelope has the specified
output. They do not currently prove existence of an operating point or derive
the supply envelope.

The `load_mos1` proof command requires that validation step to succeed.
Circuit ports written with `node!` are checked against the resulting literal
circuit during elaboration, and `mos1_extract` produces KCL and supply-bound
facts from `Mos1Satisfies`/`Mos1WithinSupply`; these commands add no semantic
assumptions.

ngspice applies numerical `gmin` regularization to otherwise floating internal
nodes. Consequently its low outputs are about 12.5 nV rather than mathematical
zero. The harness checks those floating-point results against logic bands; it
is not yet a proof that Newton iteration plus `gmin` refines
`Mos1Satisfies`.

## Open refinement obligations

The following arrows are specifications, not completed proofs:

```text
quantum transport -> Boltzmann -> drift-diffusion -> MOS1
ngspice numerical operating point -> formal MOS1 satisfying state
flattened transistor hierarchy -> composed local MOS1 observations
```

MOS1 is phenomenological, so the drift-diffusion-to-MOS1 arrow should normally
be a bounded observable refinement over a stated geometry, bias range,
temperature, and calibrated parameter set, not exact equality. A complete
"from microscopic physics" claim also needs the accumulated error to remain
inside explicit input/output noise margins.

Accordingly, the current result may be described as "proved from the stated
MOS1 compact-model equations and Kirchhoff's current law all the way through
arbitrary-width addition." It must not yet be described as "proved from
quantum transport" or as a verified implementation of ngspice's numerical
algorithm.
