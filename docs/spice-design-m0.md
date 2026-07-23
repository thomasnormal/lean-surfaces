# SPICE lane — M0 design contract (exact DC + hierarchy vertical slice)

Authoritative interface contract for the third language lane: analog
circuits via SPICE netlists, over **exact rational arithmetic**. Components
built against it must match it exactly; genuine contradictions are resolved
minimally and reported. Companion reading: `docs/sv-design-m0.md` (the
contract style this mirrors), `docs/spice-envelope-schema.md` (the extractor
payload, normative for the ingester), `docs/DESIGN.md` (Python-lane
precedent).

Toolchain: Lean v4.33.0-rc1, **core only** — no Mathlib, no real numbers.
`bash tools/ci.sh` green at the end of every phase.

## CONCURRENCY RULES (the py_vcgen workflow is active in this repo)

SPICE lane agents may create/edit ONLY: `extractors/spice/**`,
`LeanModels/Spice/**` (new), `Examples/{divider,chain,r2r}/**` (new),
`harness/spice/**`, `docs/spice-*.md`, `tools/ci.sh` (one additive
maybe-step), `.github/workflows/ci.yml` (one additive ngspice apt step),
`README.md` (ONE section, Verify phase only), `LeanModels.lean` (one import
line, integration time only). FORBIDDEN: `LeanModels/Python/VC*`,
`LeanModels/Python/VCTactic*`, proof internals of
`Examples/{nested_flow,tri,gcd,sum_to,rsa_inverse}`, `docs/reference.md`,
`AGENTS.md` (py_vcgen owns those), and everything else not listed. Never
`git commit`; scratch in `/tmp`.

## The stance: physical laws as definitions, not axioms

`Satisfies (c : FlatNetlist) (a : Assignment) : Prop` is **defined** as

> (KCL holds at every non-ground node) ∧ (every device law holds) ∧
> (`a.volt ground = 0`)

Kirchhoff's current law and Ohm's law are the *meaning* of a netlist, the
way the SV lane's scheduler is the meaning of a module — not assumptions
about the world. Consequently there are **zero `axiom` declarations
anywhere in the lane**, and `#print axioms <thm>` reporting standard-only
(`[propext, Classical.choice, Quot.sound]` or fewer) is a verify gate on
every named theorem. Never `sorry`/`admit`/`native_decide`.

## Numbers

Core `Rat` (ℚ). Linear DC circuits over rational component values have
exactly rational solutions, so the entire pipeline — netlist, MNA system,
Gaussian elimination, solution, theorem statements — is exact and
kernel-computable, and equality is decidable. The README line (Verify
phase): **ngspice (floating point) approximates our exact answers**, not
the other way round.

## M0 tier

* Elements: `R` (resistor), `V`, `I` (independent DC sources), plus `C` and
  `L` **represented** in the AST with their DC treatment: a capacitor is a
  DC open (no current, no equation), an inductor is a DC short
  (`v(n1) = v(n2)`, carries a branch-current unknown, MNA style).
* Ground: node `"0"` (exactly that string; the extractor lowercases
  identifiers; `gnd` is NOT special).
* Hierarchy **from day one** (compositional verification is the point of
  the lane): `.subckt`/`.ends` definitions and `X` instance cards in the
  extractor, schema, and AST.
* `.op` is the one supported analysis card (semantic no-op: `Satisfies` IS
  the operating point).
* Everything else — diodes, transistors, controlled sources, `.tran`,
  `.ac`, parameters — becomes an `Unsupported` card, **loud**: `flatten`
  (and hence everything downstream) refuses a netlist with a reachable
  `Unsupported` card.

## Frontend

`python3 extractors/spice/extract.py <file.cir> ...` (stdlib only,
hand-written line-based parser) emits `<file>.json`, schema `spice-0.1` —
normative vocabulary, exact-rational value grammar (suffix table: `1k` =
1000, `1m` = 1/1000, `2.2meg` = 2200000, `470u` = 47/100000, decimals
exact: `1.5` = 3/2), and determinism guarantees in
`docs/spice-envelope-schema.md`. The extractor never fails on valid SPICE
and is unit-tested by `python3 extractors/spice/test_extract.py`.

## Core semantics (`LeanModels/Spice/**`, namespace `LeanModels.Spice`)

Normative signatures (field/argument names may vary; shapes and meanings
may not):

```lean
structure Assignment where
  volt : String → Rat  -- node voltages, keyed by node name
  cur  : String → Rat  -- branch currents, keyed by device name (V and L devices)

def Satisfies (c : FlatNetlist) (a : Assignment) : Prop :=
  (∀ n, n ∈ nodes of c → n ≠ "0" → kclSum c a n = 0)
  ∧ (∀ d, d ∈ devices of c → DeviceLaw d a)
  ∧ a.volt "0" = 0
```

`FlatNetlist` is the hierarchy-free device list (only R/C/L/V/I cards; `Op`
dropped; no subckts, no instances). `kclSum c a n` is the sum over all
devices of the current each contributes INTO node `n`:

| device (card `[n₁, n₂]`, value `w`) | current into `n₁` | current into `n₂` | separate law |
|---|---|---|---|
| `R` | `(a.volt n₂ − a.volt n₁) / w` | `(a.volt n₁ − a.volt n₂) / w` | — (Ohm's law is the KCL contribution; `WellPosed` requires `w ≠ 0`) |
| `V` (n₁ = `+`) | `− a.cur name` | `a.cur name` | `a.volt n₁ − a.volt n₂ = w` |
| `I` (n₁ = `+`) | `− w` | `w` | — |
| `C` | `0` | `0` | — (DC open) |
| `L` | `− a.cur name` | `a.cur name` | `a.volt n₁ = a.volt n₂` (DC short) |

Orientation is the SPICE convention: through-currents flow from `n₁`
through the device to `n₂`; for sources, positive current through the
source flows from the `+` node to the `−` node, so a delivering V-source
has **negative** branch current — this reproduces ngspice's `v1#branch`
signs exactly (divider: `i(v1) = −1/600`, ngspice prints `-1.66667e-03`).

KCL is imposed at every node **except** ground (standard MNA; the ground
row is redundant). `Satisfies` mentions only the netlist's own nodes and
device names, so on a concrete `c` and `a` it is a finite conjunction of
`Rat` equations: provide the `Decidable` instance and prove concrete-run
facts by kernel evaluation (`decide`), never `native_decide`.

`WellPosed c : Prop` (semantics agent formalizes): the extractor-level
side conditions — all `R` values nonzero, device names unique (at minimum
the `cur`-keyed ones), every node connected so the MNA matrix is
nonsingular — packaged as "the MNA system has exactly one solution on the
netlist's support" (see Solver). Uniqueness is **on-support**: two
satisfying assignments agree on the netlist's nodes and branch keys
(`Assignment` is a total function; off-support values are junk and no
theorem may depend on them).

## Hierarchy: `flatten` is the semantic ground truth

```lean
def flatten : Netlist → Except FlattenError FlatNetlist  -- computable, total
```

Recursive instantiation with node renaming, matching ngspice's native
convention (`x1.n0` — verified against ngspice 46 output):

* An instance `X` named `x` of subckt `s` with connections `c₁…cₖ`: flatten
  `s`'s body recursively, then rename — formal port `pᵢ ↦ cᵢ`; ground
  `"0" ↦ "0"` (**global, never renamed**); every other internal node
  `n ↦ "x.n"`; every internal device name `d ↦ "x.d"` (keeps
  branch-current keys unique). Nested instance paths accumulate:
  `"x1.x2.n"`.
* Errors (detected, loud): `.missingSubckt` (no top-level definition),
  `.recursion` (instantiation cycle — seen-set on the definition path),
  `.portArity` (connections ≠ ports length), `.nestedSubckt` (a `Subckt`
  card inside a body — the extractor preserves nested definitions
  syntactically, M0 flatten rejects them), `.unsupported` (a reachable
  `Unsupported` card).
* Deterministic; structurally/fuel-bounded total function — never
  `partial`, no axioms.

**Satisfaction for hierarchical `c` goes through flatten** (definitional):
`c ⊨ a` iff `flatten c = .ok f` and `Satisfies f a`. ngspice flattens
subckts natively, so the harness cross-checks our `flatten` + solve against
its flat solve on the same file, internal nodes included.

## The central objects: port contracts

A linear block's EXACT interface abstraction — not an approximation, an
equality of behaviors:

```lean
structure PortContract (k : Nat) (Value : Type := Rat) where
  Y : Matrix k k Value -- port admittance
  J : Vec k Value      -- source term
-- port relation: I = Y ⬝ V + J
```

Core has no `Matrix`/`Vec`: choose a concrete representation
(`Fin k → Fin k → Rat` / `Fin k → Rat`, or `Array`s sized by hypothesis —
semantics agent's choice, **document it in the code**; the meaning below is
what is normative).

Conventions: `V i` = voltage of the block's `i`-th port node, referenced to
global ground; `I i` = current flowing INTO the block through port `i` from
the environment. The block's **port behavior** is the projection of its
`Satisfies`-set onto the ports:

```lean
def PortBehavior (blk : Subckt) (V I : Vec k Rat) : Prop :=
  ∃ a : Assignment,
    (∀ i, a.volt (blk.ports.get i) = V i) ∧ a.volt "0" = 0 ∧
    (∀ d ∈ devices of blk's flattened body, DeviceLaw d a) ∧
    (∀ n, n internal (non-port, non-ground) → kclSum a n = 0) ∧
    (∀ i, kclSum a (blk.ports.get i) + I i = 0)
    -- KCL at a port closes with the EXTERNAL injection I i

def HasContract (blk : Subckt) (C : PortContract k) : Prop :=
  ∀ V I, PortBehavior blk V I ↔ I = C.Y ⬝ V + C.J
```

`HasContract` is stated as an **equality of sets — both inclusions,
spelled out**:

* `→` (**soundness** of the abstraction): every port pair the block can
  realize lies on the affine set `{(V, I) | I = Y⬝V + J}`. This is what
  lets a composite theorem *discard internals*.
* `←` (**realizability**): every point of the affine set extends to a full
  internal assignment. This is what makes contracts *composable* — when a
  neighbor block demands a port point, this block can actually supply it.

Local per-block theorems (`section_contract`, …) prove `HasContract` by the
same MNA elimination, internals then discarded. Worked contract (the chain
section, `attn`: series 1k from `a` to `b`, shunt 6k from `b` to ground):

```
Y_attn = ⎡  1/1000   −1/1000 ⎤     J_attn = ⎡ 0 ⎤
         ⎣ −1/1000    7/6000 ⎦              ⎣ 0 ⎦
```

`reduceLeaf blk k` performs this reduction computably with exact arithmetic:
it fixes every port voltage to zero to obtain `J`, then performs one unit-basis
drive per port to obtain the columns of `Y`. Each drive is an ordinary checked
MNA solve. The returned matrix is computational evidence; the generic
`hasContract_of_leafCertificate` theorem turns a proof-carrying reduction
certificate into both `HasContract.sound` and `HasContract.realize`. Tests
check that reducing the extracted `attn` block returns the hand-derived matrix
above exactly.

**M0 composition metatheorem.** `CascadeBehavior` existentially wires the
output port of one two-port block to the input port of another (equal shared
voltage, currents into the two blocks summing to zero). `cascade` computes
the exact 2x2 Schur complement, and `cascade_contracts` proves, in both
directions, that `CascadeBehavior` is exactly the affine relation described
by that contract. The reverse direction explicitly consumes both blocks'
`HasContract.realize` fields, so composition is not projection-only.

The result is deliberately a theorem about the composite **behavior**, not
`HasContract` for a fabricated `Subckt`: M0 has no capture-avoiding AST
wiring/renaming constructor that could build such a value honestly. Adding
that constructor and lifting `cascade_contracts` to a physical composed
`Subckt` is deferred; no theorem may pretend it already exists. The public
workflow name `compose_contracts` is an alias of this exact behavioral theorem.

## Solver

Exact Gaussian elimination over `Rat`, computable, in Lean:

* Build the MNA system for a `FlatNetlist`: unknowns = non-ground node
  voltages + branch currents of `V`/`L` devices; equations = KCL rows +
  device-law rows.
* `solve : FlatNetlist → Except SolveError Assignment` runs total exact
  Gauss–Jordan elimination and rejects zero resistances, duplicate MNA branch
  names, and singular matrices.
* **Generic soundness**: `solve_satisfies` follows from a final evaluation of
  the definitional `Satisfies` predicate on the candidate. Thus matrix assembly
  and elimination are not trusted.
* **Uniqueness per circuit**: example proofs establish that any two satisfying
  assignments agree on the netlist's support (`WellPosed`) by exact rational
  algebra. A reusable generic nonsingularity certificate is deferred.
* Symbolic COMPONENT values are a **stretch goal only** (attempt
  `divider_formula` late; report honestly if it doesn't land). The ∀-N
  showpiece needs induction over STRUCTURE with concrete values — fully
  kernel-computable; do not block on symbolic elimination.

## Examples (three-file layout + lane-agnostic `proofs` tactic)

`Examples/<name>/{<name>.cir, <name>.json, spec.lean, proof.lean}` —
`spec.lean` holds envelope certification (ingested envelope ==
hand-built/generated literal, `hasUnsupported` check, mirroring
`Examples/counter/spec.lean`), non-vacuity `#eval`/`#guard` runs, and every
theorem STATEMENT proved `:= by proofs` (the tactic from
`LeanModels/Python/Surface.lean` is lane-agnostic); `proof.lean` holds the
real proofs. All `.cir` files are ngspice-46-prevalidated; the `.op`
results are recorded as comments in the file itself.

1. **divider** (leaf case, no hierarchy): 5V into 1k/2k.
   `divider_out : ∀ a, Satisfies (flatten divider) a → a.volt "out" = 10/3`
   (universal over ALL satisfying assignments), plus `WellPosed divider`
   (existence + on-support uniqueness). ngspice: `out = 3.333333e+00`,
   exact `10/3`.
2. **chain** — THE SHOWPIECE. `attn` = the 2-port L-section above.
   `chain : Nat → Netlist` constructs the actual hierarchical family from N
   instances of that extracted definition; an N=5 `#spice_check`, beyond the
   three committed ngspice instances, validates flattening and exact solving.
   `section_contract` proves the extracted leaf once. `LoadedChain` is the
   recursive boundary relation for N copies followed by a 3k termination;
   each step wires equal voltage and opposite interface current and exposes
   no internal assignment. `chain_contract` proves **∀ N** that the boundary
   behavior is exactly output `(2/3)^N * input` and input current
   `input/3000`; `chain_attenuates` specializes the drive to 5V. Section design
   rationale: `attn` has iterative impedance
   `Z = 1k + (6k ∥ Z) ⇒ Z = 3k`; terminated in 3k every section sees 3k
   looking right, so each stage's loaded ratio is
   `(6k ∥ 3k)/(1k + 6k ∥ 3k) = 2/3` independent of the number of
   downstream sections. ngspice (N = 1, 2, 3 committed in `chain.cir`):
   `out1/out2/out3 = 3.333333 / 2.222222 / 1.481481` = exact
   `10/3, 20/9, 40/27`.
3. **r2r** — 4-bit R-2R DAC subckt (R = 1k, 2R = 2k, MSB at `out`) with a
   **drive-assumption guarantee**: `∀ b : Fin 4 → Bool`, when the bit
   inputs are driven at `(if b i then 5 else 0)` volts,
   `a.volt "out" = 5 * binVal b / 16` where
   `binVal b = 8*b3 + 4*b2 + 2*b1 + b0` (bit `i` of `b` = ladder input
   `bᵢ`). Proof: 16-way case split, kernel arithmetic per case. This is
   the mixed-signal-ready contract; the SV-counter ramp theorem is **M1**
   (below), not built now. ngspice: pattern 1010 → `3.125` = `25/8`;
   0001 → `5/16`; 1111 → `75/16`; 0110 → `15/8`.

## Differential harness vs ngspice 46

`harness/spice/diff_test.py` (+ a small cases list). Oracle:
`~/.local/bin/ngspice` (or `ngspice` on `PATH` — CI installs it via the
additive apt step in `.github/workflows/ci.yml`), batch mode
(`ngspice -b <file.cir>`), the committed `.cir` files already contain
`.op`. Parse the batch node-voltage table (and `#branch` currents); compare
against our `flatten` + `solve` at **1e-6 relative** tolerance, printing
the EXACT rational beside ngspice's float, e.g.
`out: exact 10/3 (= 3.33333333...) vs ngspice 3.333333e+00  OK`.
ngspice flattens subckts natively and names internals `x1.n0` — our
`inst.node` renaming matches, so composite cases cross-check hierarchical
flattening node-for-node, internals included. `tools/ci.sh` gets one
additive `maybe`-step gated on ngspice's presence (mirroring the SV
harness pattern); a mismatch under ngspice is a hard failure.

The harness also covers a resistor directly across a voltage source, a current
source driving a divider, and a floating resistor network. For the last case,
Lean's exact solver returns `.singular`; ngspice exits successfully after a
fallback operating-point attempt but emits `singular matrix`, so the harness
classifies the two outcomes together instead of accepting ngspice's arbitrary
zero-voltage fallback as a unique solution.

## Definition of done (M0)

1. Extractor deterministic (double-run byte-identical), suffix unit tests
   green, all three examples extract **Unsupported-free**; schema doc
   written; `Unsupported` path exercised in tests (diode, `.tran`,
   `PULSE`, params). *(Delivered by the Contract phase.)*
2. Every `LeanModels/Spice/*.lean` green; **zero `axiom` declarations in
   the lane**; `#print axioms` standard-only on every named theorem
   (verify gate); no `sorry`/`admit`/`native_decide`; `flatten` and
   `solve` total functions (no `partial`).
3. `divider_out` + `WellPosed divider` proved.
4. `section_contract`, behavioral `chain_contract` (∀ N, by induction over
   boundary composition), `chain_attenuates` (exact `(2/3)^N * 5`)
   proved — the ∀-N showpiece.
5. The r2r drive-assumption theorem proved for all 16 bit vectors.
6. `HasContract` stated as the double inclusion; `reduceLeaf` computes exact
   matrices; `compose_contracts`/`cascade_contracts` are proved with
   contracts-only data flow. Physical AST composition remains deferred until
   a capture-avoiding wiring constructor exists.
7. Harness green vs ngspice 46 on all three netlists plus the edge and singular
   cases (node voltages and recorded branch currents).
8. `bash tools/ci.sh` green; the Python and SV lanes untouched and green;
   `LeanModels.lean` gains exactly one import line; README gains exactly
   one section (Verify phase) including the line: ngspice approximates
   our exact answers.

## M1 (deferred — listed so nobody builds them now)

* **Mixed-signal ramp**: the SV lane's verified counter driving the r2r
  DAC bits; theorem: the sampled analog output is the exact staircase
  `5 * (count mod 16) / 16`. The r2r drive-assumption contract above is
  the designed-in hook.
* **Symbolic component values**: `divider_formula`
  (`v(out) = E * R2 / (R1 + R2)` with symbolic `R1 R2 : Rat`, side
  conditions `R1 + R2 ≠ 0`) — requires symbolic elimination; stretch goal,
  attempted late in M0 at most, reported honestly.
* **AC analysis over Gaussian rationals** ℚ(i): impedances as pairs
  (re, im), same exact-elimination story; caps/inductors get their
  frequency-domain laws.
* `.tran` (needs real/interval numerics or exact event sequences),
  nonlinear devices (D/Q/M), controlled sources (E/G/F/H), `.param`,
  `.include`, `.model`.
