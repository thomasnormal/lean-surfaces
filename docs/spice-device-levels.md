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
| Loaded compact transistor | `LoadedInverterBehavior` | explicit conservative load charge, absolutely-continuous MOS1/capacitor DAE, and correlated PVT world |
| Thin dynamic storage | `Dram1T1CBehavior` | open NMOS access port, explicit storage charge, hold and write-zero transient modes |
| Static CMOS logic | `Mos1AndEquations`, `Mos1OrEquations`, `Mos1InverterEquations` | bounded internal node voltages and local KCL |
| Arithmetic blocks | `Mos1HalfAdderContract`, `RippleAdderOf` | rail-valued half-adder observations and width-parametric composition |

The transport specifications deliberately contain no existence, uniqueness,
discretization, or solver claims.

## Proved vertical segment

The checked segment currently starts at a restricted MOS1 DC model:

```text
extracted .model parameters and MOS cards
  -> MOS1 channel equation + driven-port/internal-KCL component laws
  -> CMOS inverter / AND / OR rail behavior
  -> extracted 20-transistor half-adder
  -> three-half-adder full-adder relation
  -> N-bit ripple arithmetic, for every N
```

The top theorem is compositional rather than a single 3,000-transistor
elimination. `half_adder_mos1_correct` proves the extracted reusable block
once. `ripple_adder_mos1_correct` then proves that, for every width, a
`RippleAdderOf` network whose component observations satisfy that physical
contract implements unsigned addition. Its premise contains the local MOS1
states, KCL, supply envelope, rail-valued wiring observations, and shared
Boolean port values. No ideal-switch premise occurs in this chain.

The committed driver-free 50-bit deck contains 50 literal calls to our
three-half-adder `full_adder`. `ripple_adder_literal_layout` proves that its
hierarchy expands to exactly 150 half-adder calls, and
`ripple_adder_half_adder_implementation` proves that the embedded component
matches the independently proved 20-transistor implementation after erasing
source spans. `ripple_adder_fifty_bit` then connects compositional physical
observations of those actual calls to the all-width arithmetic theorem.

A further theorem projecting every satisfying state of one flattened
3,000-transistor circuit into those local `RippleAdderOf` observations remains
open. Until that state-restriction theorem lands, the correct claim is literal
hierarchy verification plus compositional MOS1 soundness, not monolithic
elimination of the flattened deck.

The deck profile is explicit: `LEVEL=1`, `VTO=1/-1`, positive `KP`,
`LAMBDA=0`, `IS=0`, omitted device dimensions (`W/L=1`), steady DC, no gate
or body current, source-oriented channels, and all observed nodes within the
0--5 V supply envelope. The shared circuit's resolved MOS1 projection rejects
a deck that does not provide this profile. Successful validation produces a
`Mos1ResolvedCircuit`: node, voltage
source, transistor, and model identifiers have distinct Lean types; every
transistor contains its resolved `Mos1Model`; and the required parameters are
named structure fields rather than a string-keyed array. The logic contracts
are soundness results: any satisfying state in the envelope has the specified
output. `half_adder_mos1_observation_exists` also gives an exact rail-valued
local operating-point witness for each Boolean input vector. The supply
envelope itself is still a named premise, not a derived global invariant.

The `load_circuit` proof command parses the `.cir` source directly in
Lean and requires that typed MOS1 validation succeed. Circuit ports written
with `node!` are checked against the resulting literal circuit during
elaboration, and `mos1_extract` produces KCL and supply-bound facts from
`Mos1Satisfies`/`Mos1WithinSupply`; these commands add no semantic assumptions.
Reusable component decks omit testbench voltage sources, and
`Mos1ComponentSatisfies` exempts only explicitly driven input and supply ports
from KCL. This prevents a fixed test vector from making a reusable gate
contract vacuous.

The loaded inverter applies the same rule dynamically. Its `.cir` file
contains only the PMOS, NMOS, and output capacitor. A typed adapter checks
that topology and resolves its models; supply, held input, initial voltage,
and horizon are run-world fields. Lean proves DC existence, finite-horizon
DAE existence, rail invariance, no overshoot, an exponential settling
envelope, and zero static channel current at rail inputs. The MOS1 profile
declares zero intrinsic terminal charge; the explicit capacitor supplies the
conservative dynamic storage. These are compact-model theorems, not evidence
that the profile covers a fabricated process.

The first 1T1C DRAM slice uses the same charge and DAE semantics. Only its
write-zero mode is derived from the device law: the write DAE field is proved
equal to the normalized MOS1 channel current. Its hold theorem is
definitional, not derived: the hold-mode field is *defined* to be zero and
constancy is asserted inside `Dram1T1CBehavior` itself, with MOS1 cutoff and
`IS=0` recorded as the modeling rationale rather than consulted as premises.
Write-one, read charge sharing, and retention with a nonzero leakage envelope
are not claimed by this thin slice. The loaded `dram_bitcell` read slice is
likewise spec-level: its charge-sharing voltage formula, ideal sense stage,
and rail restore are definitional relations, and only the sign/margin
arithmetic and the bank-width composition theorems are derived from them.

Ngspice and Spectre apply numerical regularization to otherwise floating
internal nodes. Consequently low outputs are about 12.5 nV rather than
mathematical zero. Both harnesses check those floating-point results against
logic bands, including all AND/half-adder vectors and four 50-bit-adder
vectors. They also check rising and falling loaded-inverter traces against the
proved bounded, monotone exponential envelope. This agreement is not yet a
proof that either simulator's Newton iteration, transient integration, and
regularization refine the formal semantics.

## Open refinement obligations

The following arrows are specifications, not completed proofs:

```text
quantum transport -> Boltzmann -> drift-diffusion -> MOS1
simulator numerical operating point -> formal MOS1 satisfying state
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
quantum transport" or as a verified implementation of ngspice's or Spectre's
numerical algorithm.
