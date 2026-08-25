import LeanModels.Sv.Step
-- `Region` (the IEEE 1800 §4.4 event regions) lives in Regions.lean, which
-- NOTHING in Step's chain reaches: Step -> SelfCheck/Obs -> Semantics -> Ast.
-- `SvWorld.regionQ` and `curRegion` are indexed by it, so this import is
-- load-bearing rather than tidiness.
import LeanModels.Sv.Regions
import LeanModels.Core.Outcome

/-!
# R1 inch 4a-0 — the SV tier on the family substrate

The four pieces `docs/family-architecture.md` §3.4 asks every tier for,
instantiated for SystemVerilog: the world `W`, the tier's own raise `ρ`,
the refusal payload `π`, and the snapshot `σ`.

**No semantics lands here.** There is no `slotStep` and no `runRegion`;
this is the plumbing those will be written against, plus the two
adoption facts that let the existing estate come along unchanged.

## Why `W` is big, and why that is not a defect

`SvWorld` carries a process table, per-region ready sets, two nonblocking
write buffers, a time wheel and an output buffer. The substrate was never
meant to shrink the semantics — only to standardise its plumbing and its
proof interface. A stratified event scheduler has a lot of state because
IEEE 1800 §4.4 says it does.

The process table is the load-bearing part. `SemMWith` **cannot
suspend**: `ExceptT ρ (StateT W Halt) α` unfolds to `W → (Except ρ α × W)`
— an `α`, or a `ρ`, plus a `W`, and no third case. So a process that
pauses mid-body at `@`/`#`/`wait` cannot express that as an *effect*; the
continuation is **data in `W`** (`ProcState.residual`) and suspension is a
**return value** (`StepOutcome`, `LeanModels/Sv/Step.lean`). This is sound
because SV's suspension points are syntactic, so "where it paused" is a
position in the program text rather than an arbitrary closure. The family
document records the general form of this at §(1a).
-/

namespace LeanModels.Sv

open SelfCheck

set_option autoImplicit false

/-! ## π — the refusal payload -/

/-- A pointer into IEEE 1800 — the `π` every refusal carries.

A refusal that cannot name the clause it refuses under is one a human
cannot act on and a scoreboard cannot bucket without parsing prose. SV has
a single normative document, so this is one field where Go's `SpecRef`
needs two. No IEEE text is reproduced: this is a citation, never a quote. -/
structure SvClause where
  /-- The clause or subclause, e.g. `"4.4"` (scheduling regions),
  `"11.4.3"` (whole-vector arithmetic collapse). -/
  clause : String
deriving Repr, DecidableEq, Inhabited

/-! ## ρ — the tier's own raise -/

/-- `$finish` / `$stop`: simulation ends, **and the state survives**.

This is `ρ`, not `Loud`, and the distinction is load-bearing rather than
stylistic. `SvWorld.out` holds the `$display` text, which for **97% of the
conformance corpus IS the test's verdict** — the `PASS`/`FAIL` line. A
`Loud` halt discards the world; `ExceptT ρ` keeps it. Putting `$finish` in
the wrong layer would silently throw away the answer the run exists to
produce. Same reasoning as the C tier's `abort`/`exit` split. -/
inductive Finish where
  | finish
  | stop
deriving Repr, DecidableEq, Inhabited

/-! ## The refusal classes, and the one that is SV's -/

/-- How this tier refuses, mapped onto the family's four causes.

**`race` is the interesting one.** IEEE 1800 §4.7-4.8 leaves the order of
ready processes *within* a region unspecified, so a design whose result
depends on that order has no single answer — and `orderDependence` is the
family cause that says exactly this. It arrived in `Core` from ES, Go and
Python without SV asking, and it is precisely the class this tier's
taxonomy predicted it would need.

**What is deliberately NOT here: x-propagation.** Four-state unknown is a
VALUE, not a refusal. `lx`/`lz` flow through the `LVec` operators by
tabulated per-operator rules, never short-circuit, and an x-carrying
result is a **successful** run. Modelling x in the `ExceptT` layer — a
natural-looking move, since "unknown" reads like "exceptional" — would
convert 4-state semantics into 2-state-plus-errors and destroy the value
model. `ρ` is `$finish` and `$stop`; `RefusalCause` is the four below;
`x` is neither. -/
inductive SvRefusal where
  /-- Construct outside the modelled fragment. Retires by climbing a rung. -/
  | outOfTier
  /-- IEEE 1800 says the result is an error, not a value — e.g. multiple
  continuous drivers on a variable. Never retires. -/
  | illegal
  /-- Same-region ordering the standard leaves free (§4.7-4.8): the design
  has no single outcome. Never retires by building more language. -/
  | race
  /-- Unmodelled system task or DPI import. Retires by widening the slice. -/
  | environment
deriving Repr, DecidableEq, Inhabited

/-- The image of this tier's refusal in the family's four causes. -/
def SvRefusal.toCore (r : SvRefusal) (c : SvClause) : RefusalCause SvClause :=
  match r with
  | .outOfTier   => .unsupported c
  | .illegal     => .undefined c
  | .race        => .orderDependence c
  | .environment => .environment c

/-! ## W — the scheduler-shaped world -/

/-- Why a process is not currently runnable. -/
inductive ProcStatus where
  | ready
  | suspended (t : Trigger)
  | finished
deriving Repr, Inhabited

/-- One process's state. `residual` is the DEFUNCTIONALIZED CONTINUATION:
the statements that still have to run when its trigger fires. -/
structure ProcState where
  residual : List SStmt
  status : ProcStatus
  /-- What to reinstate when this process COMPLETES.

  `none` runs once — an `initial` block finishes and stays finished.
  `some body` RE-ARMS — an `always_ff @(posedge clk) body` is
  `forever { @(posedge clk); body }`, so completing its body is not the end
  of the process, it is the end of one iteration.

  Without this field a completed `always` was marked `.finished` forever,
  which produced a SHORTER TRACE rather than an error — the failure mode
  nobody notices. -/
  arm : Option (List SStmt) := none
deriving Repr, Inhabited

/-- The world — `W`.

Shaped for IEEE 1800 §4.4 rather than for the cycle model, deliberately:
the cycle model is a *projection* of clause 4 (`cycleOf`), so a `W`
designed for the projection would have to be redesigned when the regions
arrive. Fields beyond 4a's own coverage are reserved now because reserving
them is cheap and retrofitting them is not. -/
structure SvWorld where
  /-- Simulation time — the wheel's "now". -/
  time : Nat := 0
  /-- The 4-state signal environment. -/
  signals : SvState := []
  /-- The process table. -/
  procs : Array ProcState := #[]
  /-- Ready set per region; the oracle orders WITHIN one of these. -/
  regionQ : Region → List Nat := fun _ => []
  /-- Which region is executing. -/
  curRegion : Region := .active
  /-- Nonblocking write buffer (Active-evaluated, NBA-committed). -/
  nba : NbaQueue := []
  /-- The reactive family's nonblocking buffer (Re-NBA). -/
  reNba : NbaQueue := []
  /-- The time wheel: `(wake time, process index)`. -/
  future : List (Nat × Nat) := []
  /-- `$display`/`$write` output. For most of the corpus this IS the
  verdict, which is why `$finish` must preserve it. -/
  out : Out := {}
  /-- Oracle invocation counter. -/
  k : Nat := 0

/-! ## The tier's monad -/

/-- **The SV tier's instantiation of the family monad.**

`W = SvWorld`, `ρ = Finish` (state-preserving), `π = SvClause` (the
refusal's citation), `σ = Unit` (no diagnostic snapshot yet).

The schedule oracle is deliberately **NOT** in here. It stays a parameter
of the definitions (`runRegion σ …`), because a schedule threaded through
the state becomes a choice the program MAKES rather than one quantified
OVER — and every race theorem in this tier is stated as `∀ σ`. -/
abbrev SvM := SemMWith SvWorld Finish SvClause Unit

/-- The only way this tier refuses: a class, a clause, and prose. -/
def refuseSv {α : Type} (r : SvRefusal) (c : SvClause) (msg : String) : SvM α :=
  LeanModels.refuse (r.toCore c) msg

/-! ## The adoption facts

Two one-line facts that let the EXISTING estate come along unchanged
rather than be re-proved. Both are `rfl`, which is the point: adoption by
iff costs nothing and touches no proof. -/

/-- **`Res.le` IS Core's `FlatLe` at `timeout`.**

Adopted BY IFF, keeping `Res.le`'s spelling and its `⊑` notation — the
`LeanModels/Python/Obs.lean` precedent, whose own note gives the reason:
stated as an iff rather than a redefinition so that the spelling, the
notation and every consumer stay put, and the tree gains the shared name
additively.

That matters concretely here: `Res.le` carries this tier's
fuel-monotonicity ladder (`evalExpr_le` → … → `run_le`), so an iff makes
SV a `FlatLe` instance while every one of those proofs keeps working. A
rename would have re-opened all of them for nothing. `Res.timeout_le` and
the `⊑` congruences already live in `Obs.lean` and are deliberately NOT
restated here — they are tier-local, because `Sv.Res` and `Python.Res` are
different types. -/
theorem Res.le_iff_flatLe {α : Type} {x y : Res α} :
    x ⊑ y ↔ FlatLe .timeout x y := Iff.rfl

end LeanModels.Sv
