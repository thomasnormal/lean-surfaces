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
| Thin dynamic storage | `Dram1T1CBehavior`, `DramWriteBehavior` | open NMOS access port, explicit storage charge, hold/write-zero modes, and a source-derived write-one DAE |
| Differential regeneration | `DramDifferentialSenseBehavior` | source-projected cross-coupled CMOS latch, two capacitor/KCL equations, rail/metastable equilibria, and an exact balanced differential-mode reduction |
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

The first 1T1C DRAM slice uses the same charge and DAE semantics. Its
write-zero mode is derived from the device law: the write DAE field is proved
equal to the normalized MOS1 channel current. In hold mode, the zero field is
the ideal zero-leakage model choice, but constancy is now a theorem derived
from the DAE and initial condition rather than a premise of
`Dram1T1CBehavior`. Inside the nonnegative rail domain,
`dram1T1C_holdField_eq_mos1` proves that field equals the capacitor KCL field
obtained from the bidirectional MOS1 access device with its wordline low.
`IS=0` remains the explicit no-leakage compact-model restriction.

Write-one is represented by the separate, physics-only `DramWriteProgram`.
The literal open cell deck supplies its threshold, transconductance, and
storage capacitance through a checked `SourceBinding`; wordline, bitline,
initial storage, and horizon remain world fields. Lean derives the complete
piecewise write field from `mos1TerminalCurrent` and capacitor KCL, proves the
closed-form trace absolutely continuous and satisfying that field, and proves
every other admitted trace equal to it. Thus every trajectory from 0 V
reaches `[3 V, 4 V]` within 1 ns without exceeding 4 V, with paired
realizability and domain closure. Exact finite-time arrival at 4 V is neither
assumed nor claimed: the static MOS1 equations admit every voltage in the
threshold-loss interval as an equilibrium, and the kernel exhibits both
4 V and 5 V as distinct nominal equilibria.

Read charge sharing and retention with a nonzero leakage envelope are not
claimed by this thin slice. The loaded `dram_bitcell` read slice is likewise
spec-level: its charge-sharing voltage formula, ideal sense stage, and rail
restore are definitional relations, and only the sign/margin arithmetic and
the bank-width composition theorems are derived from them.

The concrete `dram_bank_2x2` slice is a source-validated compositional
transient-endpoint prototype. Its adapter checks the 46-device deck. The
precharged voltage is the endpoint of a source-derived enabled-MOS1 plus
300 fF bitline-capacitor DAE. Lean proves the unique trajectory stays within
the rail domain and reaches `[2.47 V, 2.5 V]` after 10 ns; no exact
equilibrium is inserted into the behavior. The proofs propagate this
finite-time interval through bidirectional MOS1 charge sharing and static
sense decision bands. Every cell on an unselected
wordline now has a source-parameterized 1T1C hold trace; its initial condition
and zero-leakage DAE derive preservation at the connected phase endpoint.
Selected-row read restoration uses the physical MOS1/capacitor DAE for a
finite 1 ns horizon with each bitline clamped to the sense output. During a
write, unselected columns continue that source-derived trajectory while
unselected rows remain in cutoff hold. Both read restore and selected write
give `[0 V, 1 V]` for zero and `[3 V, 4 V]` for one. The read equation
manifest reports a legacy two-inverter sense endpoint contract; write imports
the preceding read endpoint phase.
Finite precharge timing is proved. The two-inverter sense path accepts
conservative low/high bands but remains a static single-ended abstraction;
its switching boundary admits a non-rail solution, and no bank-level
regenerative offset, metastability-exclusion, or sensing-time theorem is
claimed. Safety is paired with realizability and 0--5 V domain closure for
this precise relation. Independently of that static path, physical precharge
and charge sharing now prove a uniform `3/22 V` differential against an
otherwise precharged reference for either stored bit. A separate composition
module keeps fixed `BL`/`BLref` identities and proves that the nominal
four-MOS latch initially amplifies the delivered sign, with a paired
primitive-residual witness. The 2x2 deck does not instantiate that reference
line or latch connection.

The driver-free `dram_sense_amp` component is the first physical replacement
for that nominal sense contract. Its checked adapter accepts exactly four
cross-coupled MOSFETs and two capacitors, projects both model profiles and
capacitances from the embedded source, and generates a physics-only vector
DAE. Lean proves the two rail equilibria are realizable, proves the matched
midpoint is a realizable metastable behavior, and derives an exact scalar
differential-mode DAE from the primitive two-node residual. The reduction has
both residual directions on the balanced manifold, a physical-trajectory
lifting theorem, and a residual witness at every point. For
`0 < deviation < 5/2`, Lean proves the selected derivative is positive, the
complement derivative is negative, and their sum is zero. No desired
decision or endpoint occurs in its equation program. The exact exponential
trajectory `d(t) = d(0) * exp(10^9 t)` is proved to be an inhabited physical
behavior while it remains in the first MOS region, and an integrating-factor
argument proves uniqueness of the reduced scalar solution there. The named
primitive behavior stays inside the rails and reaches a requested positive
first-region margin by a derived logarithmic deadline. For arbitrary finite
horizons, Picard-Lindelof constructs a primitive trajectory across all three
nominal MOS regions from every balanced initial deviation in `[0, 5/2]`; a
proved barrier keeps that witness inside the rails. The complete five-region
source field is proved Lipschitz on every bounded interval. Since every
finite-horizon AC trajectory has bounded image, Grönwall proves uniqueness
across all regions without assuming a rail domain; comparison with the
witness then proves basin invariance and monotone regeneration for every
balanced scalar trajectory. For the primitive two-node DAE, a common-mode
energy argument derived from the four MOS laws, two capacitor laws, and KCL
proves that every rail-valid vector trajectory with balanced initial data
remains balanced. It therefore projects exactly into the scalar view and is
determinate. A separate source-backed device-order theorem covers arbitrary
common mode pointwise: at every ordered, nonterminal state in the rail
rectangle, the primitive DAE forces the voltage differential to grow.
Positive projected capacitances provide a residual witness at every such
state, so this local theorem is non-vacuous. For every finite horizon and
every nominal unbalanced initial pair in the rail square, Lean now constructs
an absolutely-continuous primitive DAE behavior. A barrier proves the
constructed pair remains in the rail square, where its globally Lipschitz
proof extension agrees exactly with the primitive MOS currents. Unbalanced
determinacy and convergence, mismatched-device behavior, offset budget,
delivered rail margin, and quantitative rail-settling bounds remain open
transient obligations. Both
ngspice and Spectre validate the two perturbed directions, but those traces
are not proof premises.

Consequently the result is not yet a proof that a physical trajectory reaches
the contracted endpoints by a deadline. Ngspice and Spectre provide
independent timing evidence only. `IS=0` also means the model derives no
physical leakage-retention or refresh bound.

`dram_bank_256x32` generalizes this endpoint argument over arbitrary
`Fin rows` and `Fin columns`, then instantiates it at 256 by 32. The concrete
hierarchical source has 8,192 cells and 32 complete per-column paths. A
fail-closed elaboration command validates the row template, every row
instance, every bitline load, all periphery instances, and the three model
profiles. Kernel-checked parameter and topology certificates derive the typed
cell/row/subarray/column/bank profile from the embedded source; the complete
`SourceCircuit.toDramBank` projection follows from those certificates. The
endpoint theorem itself is size-independent:
it proves read/write safety, realizability, domain closure, and refinement to
`DramBankStep` for an arbitrary selected address, relative to the explicitly
reported legacy sense endpoint contract above. The selected write uses the
same source-derived 1 ns logic-band trajectory theorem at every address.

Each generated column now also contains a 300 fF reference bitline, paired
transmission-gate couplers, and an isolated four-MOS/two-capacitor
differential latch with independently controlled sense rails. The source
projector validates this exact connection and derives its model and
capacitance parameters. Lean proves its primitive residual is inhabited at
every state and, after a coupling phase has established the rail-valid
fixed-polarity ordering, proves the latch locally regenerates in the correct
direction. Lean also constructs the transmission-gate trajectory from the
bank's bitline/reference bounds, proves that it satisfies the primitive
four-capacitor/MOS1 DAE, conserves pair charge, has no overshoot, stays in
`[2 V, 3 V]`, and establishes the required ordering after every positive
duration. That endpoint initializes an inhabited finite-horizon primitive
latch DAE behavior, and Lean proves both node voltages remain within
`[0 V, 5 V]` for the complete horizon. The resulting unbalanced behavior
still lacks a determinacy, convergence, and resolution-time proof, and
restore remains an imported endpoint phase. Consequently this source-backed
path has not yet replaced the endpoint theorem's imported sense contract.

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
