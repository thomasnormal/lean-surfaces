import LeanModels.Sv.Semantics

/-!
# R1 inches 2-3 — the region TYPES, and the cycle view

The type-level half of `docs/sv-r1-scheduler.md`: the IEEE 1800-2023 §4.4
event regions, the region-aware schedule oracle, the slot-structured
trace, and the `cycleOf` abstraction through which every observation is
stated.

**No semantics lands here.** There is no `slotStep` and no `runRegion`;
those are inch 4. Everything below is types, one embedding, and the
`CycleView` class that makes a theorem's *statement text* survive the
arrival of the region semantics.

## Why this lands before the semantics

`docs/sv-r1-scheduler.md` §8.1 measured the estate a trace-type change
re-opens: **156 of 231 proof-carrying declarations (68%)** mention the
trace. The design's answer is to route every observation through
`cycleOf` so that statements are written against the *cycle view* rather
than against whichever trace type is current. For that to help, the
abstraction has to exist **before** the theorems do — hence this file,
ahead of inch 4.

## The three types, and what each is for

* `Region` — all fifteen regions of §4.4 (nine core, six PLI), complete
  from day one. The PLI constructors are uninhabited at R1 and carry no
  semantics; naming them now costs one constructor each, where adding
  them later would change the type and re-open everything a second time.

* `RegionOracle` — the oracle widened with a `Region` parameter, so a
  schedule can reorder *within* a region. This is the determinism
  boundary of §2.3 made into a type: the oracle permutes the ready list
  inside one region and never chooses the region order, the statement
  order within a process, or the NBA application order.

  It is introduced **additively**, as a new type with an embedding
  `ScheduleOracle.toRegion`, rather than by editing `ScheduleOracle` in
  place. Editing in place would break every existing `∀ σ` theorem at a
  moment when none of them can yet be re-proved against a semantics that
  does not exist. The embedding is what discharges the design's claim
  that the widening is conservative (`toRegion_choose`).

* `Slot` / `RegionTrace` — one entry per simulation time slot, recording
  `sampled` (what Preponed observed, which is what clocking blocks and
  concurrent assertions see) and `final` (the state the slot closes in,
  which is what Postponed reads and what any cycle-level observer sees).

  Deliberately **not** a per-region state sequence: nothing outside the
  slot can observe an intermediate region, so a richer trace would make
  every theorem quantify over detail no property can mention.
-/

namespace LeanModels.Sv

/-! ## The event regions (§4.4) -/

/-- The stratified event regions of IEEE 1800-2023 §4.4, in slot order.

Nine core simulation regions and six PLI callback regions. The PLI
regions are carried from day one but have no inhabitants at R1 — see the
module docstring for why they are named now rather than later. -/
inductive Region where
  /-- Sampling for concurrent assertions and clocking-block inputs: values
  read before anything in the slot changes them. -/
  | preponed
  /-- PLI callback point. -/
  | preActive
  /-- Blocking assignments, continuous-assignment and primitive
  evaluation, `$display`, and the RHS evaluation of nonblocking
  assignments. -/
  | active
  /-- Processes resumed from `#0`. -/
  | inactive
  /-- PLI callback point. -/
  | preNBA
  /-- The LHS updates of nonblocking assignments scheduled in this slot. -/
  | nba
  /-- PLI callback point. -/
  | postNBA
  /-- Concurrent-assertion property expressions; pass/fail code scheduled. -/
  | observed
  /-- PLI callback point. -/
  | postObserved
  /-- Program-block code, assertion action blocks, clocking-block drives. -/
  | reactive
  /-- `#0` within the reactive set. -/
  | reInactive
  /-- PLI callback point. -/
  | preReNBA
  /-- Nonblocking updates scheduled from the reactive set. -/
  | reNBA
  /-- PLI callback point. -/
  | postReNBA
  /-- `$strobe` and `$monitor`. Read-only: no value may change here. -/
  | postponed
deriving Repr, BEq, DecidableEq, Inhabited

namespace Region

/-- The nine core simulation regions, in slot order. -/
def core : List Region :=
  [preponed, active, inactive, nba, observed, reactive, reInactive, reNBA,
   postponed]

/-- The six PLI callback regions, in slot order. -/
def pli : List Region :=
  [preActive, preNBA, postNBA, postObserved, preReNBA, postReNBA]

/-- Every region, in the slot order of §4.4 Figure 4-1. -/
def all : List Region :=
  [preponed, preActive, active, inactive, preNBA, nba, postNBA, observed,
   postObserved, reactive, reInactive, preReNBA, reNBA, postReNBA, postponed]

/-- A PLI callback region carries no SystemVerilog execution at R1. -/
def isPLI : Region → Bool
  | preActive | preNBA | postNBA | postObserved | preReNBA | postReNBA => true
  | _ => false

/-- `postponed` is read-only (§4.4): a write scheduled here is a defect,
not a value. The semantics (inch 4) refuses rather than dropping it. -/
def isReadOnly : Region → Bool
  | postponed => true
  | _ => false

end Region

/-- The core and PLI regions partition the fifteen, and `all` is their
interleaving — checked, so the three lists cannot drift apart. -/
example : Region.core.length = 9 := by decide
example : Region.pli.length = 6 := by decide
example : Region.all.length = 15 := by decide
example : Region.all.filter (fun r => !r.isPLI) = Region.core := by decide
example : Region.all.filter Region.isPLI = Region.pli := by decide

/-! ## The region-aware oracle -/

/-- A legal schedule under the region semantics: at invocation `k`, within
region `r`, order the ready process list.

`choose_perm` is the legality proof, so `∀ σ : RegionOracle` ranges over
exactly the legal schedules — the same discipline `ScheduleOracle`
already uses, extended with the region the choice is made in.

**What this type does NOT let a schedule choose** (§2.1 of the design):
the region order, the statement order inside a process, and the order in
which nonblocking updates to one variable are applied. Those are fixed by
the standard and so are not parameters here. -/
structure RegionOracle where
  /-- Invocation counter, region, ready process indices in; execution
  order out. -/
  choose : Nat → Region → List Nat → List Nat
  /-- Every invocation yields a permutation of the ready list. -/
  choose_perm : ∀ (k : Nat) (r : Region) (ready : List Nat),
    (choose k r ready).Perm ready

/-- The widening is CONSERVATIVE: a cycle-level schedule embeds by
ignoring the region. -/
def ScheduleOracle.toRegion (σ : ScheduleOracle) : RegionOracle where
  choose := fun k _ ready => σ.choose k ready
  choose_perm := fun k _ ready => σ.choose_perm k ready

/-- The embedding preserves every choice — this is the proof obligation
behind the design's claim that adding the `Region` parameter keeps the
meaning of every existing `∀ σ` theorem. -/
theorem ScheduleOracle.toRegion_choose (σ : ScheduleOracle) (k : Nat)
    (r : Region) (ready : List Nat) :
    σ.toRegion.choose k r ready = σ.choose k ready := rfl

/-- Source/declaration order in every region. -/
def ρ_src : RegionOracle := σ_src.toRegion

/-- Reverse order in every region. -/
def ρ_rev : RegionOracle := σ_rev.toRegion

/-- Reverse only within one region, source order elsewhere — the shape a
region-local race witness needs, and something the cycle-level oracle
could not express. -/
def RegionOracle.revIn (target : Region) : RegionOracle where
  choose := fun _ r ready => if r == target then ready.reverse else ready
  choose_perm := fun _ r ready => by
    by_cases h : r == target
    · simp [h, List.reverse_perm]
    · simp [h]

instance : Inhabited RegionOracle := ⟨ρ_src⟩

/-! ## The slot-structured trace -/

/-- One simulation time slot.

`sampled` is what the Preponed region observed — the pre-slot values that
clocking blocks and concurrent assertions read. `final` is the state the
slot closes in, which is what Postponed reads and what a cycle-level
observer sees. -/
structure Slot where
  /-- Simulation time at which this slot ran. -/
  time : Nat
  /-- Preponed sample: values as of before any activity in the slot. -/
  sampled : SvState
  /-- The state the slot closes in. -/
  final : SvState
deriving Repr, Inhabited

/-- A run under the region semantics: one entry per time slot. -/
abbrev RegionTrace := List Slot

/-! ## `cycleOf` — the abstraction every observation goes through

The mechanism that makes a theorem's statement text survive inch 4. A
property is stated against the CYCLE VIEW of a trace, never against a
trace type directly; `cycleOf` is the identity on today's cycle traces
and the per-slot projection on region traces, so the same statement
elaborates before and after the region semantics arrives. -/

/-- Types that admit a cycle-level view. -/
class CycleView (τ : Type) where
  /-- The sequence of states a cycle-level observer sees. -/
  cycleOf : τ → List SvState

/-- The cycle view of a trace. -/
def cycleOf {τ : Type} [CycleView τ] (t : τ) : List SvState :=
  CycleView.cycleOf t

/-- **The stub.** Today the cycle semantics IS the cycle view, so `cycleOf`
is the identity — which is exactly what lets rung A's divider theorem be
written in its final form against `run` before `runRegion` exists. -/
instance : CycleView (List SvState) where
  cycleOf := id

/-- **The real projection.** A slot is observed by the state it closes in. -/
instance : CycleView RegionTrace where
  cycleOf := fun tr => tr.map (·.final)

@[simp] theorem cycleOf_cycle (tr : List SvState) : cycleOf tr = tr := rfl

@[simp] theorem cycleOf_region (tr : RegionTrace) :
    cycleOf tr = tr.map (·.final) := rfl

/-! ## The cycle-level fragment

The predicate the adequacy lemma (inch 5) is stated over. Everything
outside it extracts to `Process.unsupported` today and the semantics
refuses on it — which is what makes R1 a conservative EXTENSION rather
than a supersession: outside the fragment the cycle model gives no
answer, so there is nothing to contradict. -/

/-- A process outside the M0 tier's four supported kinds. -/
def Process.isUnsupported : Process → Bool
  | .unsupported _ _ => true
  | _ => false

/-- The cycle-level fragment: every process is one the M0 tier supports.
Decidable, so `decide` settles it on any concrete design. -/
def Design.isCycleFragment (d : Design) : Bool :=
  d.processes.all fun p => !p.isUnsupported

/-! ## The divider observable — rung A's statement shape

Written against the CYCLE VIEW, so the theorem text does not mention
`run`, `cycleStep`, `Slot` or `RegionTrace`, and does not change when
inch 4 lands. See `docs/sv-r1-scheduler.md` §6. -/

/-- The value of `target` in the first state where `trigger` reads as a
known 1.

Four-state-honest by construction: an `x`/`z` on the trigger is **not** a
trigger (`toNat?` is `none`), so an unknown handshake never silently
yields a result — the tier refuses to observe rather than guessing. -/
def sampleAtFirst (tr : List SvState) (trigger target : String) :
    Option LVec :=
  match tr.find? (fun st => ((st.lookup trigger).bind LVec.toNat?) == some 1) with
  | some st => st.lookup target
  | none => none

/-- A serial divider's result: the quotient signal sampled in the first
cycle where the done signal is asserted.

**The shape rung A must be written in.** It takes any `CycleView`, so the
identical statement elaborates against today's `List SvState` traces and
against `RegionTrace` after inch 4 — only the instance changes, and the
adequacy lemma discharges the difference.

The signal names are parameters because the intended instantiation is
OpenHW's `cv32e40p_alu_div` (already ingested at `sv-0.2`, and the module
rung A targets), whose handshake is `OutVld_SO` with the quotient on
`Res_DO`:

    divResult tr "OutVld_SO" "Res_DO"

Its `OpCode_SI` selects among udiv/urem/div/rem, so rung A's statement
will carry that as a hypothesis rather than baking one operation in. -/
def divResult {τ : Type} [CycleView τ] (t : τ) (doneSig quotSig : String) :
    Option LVec :=
  sampleAtFirst (cycleOf t) doneSig quotSig

/-! ## Guards -/

section Guards

private def bitv (n w : Nat) : LVec := LVec.ofNat w n

private def stX : SvState := [("ready_o", bitv 0 1), ("result_o", bitv 0 8)]
private def stDone : SvState := [("ready_o", bitv 1 1), ("result_o", bitv 7 8)]
private def stLater : SvState := [("ready_o", bitv 1 1), ("result_o", bitv 9 8)]

private def cyc : List SvState := [stX, stDone, stLater]
private def reg : RegionTrace :=
  [⟨0, stX, stX⟩, ⟨10, stX, stDone⟩, ⟨20, stDone, stLater⟩]

-- The region trace projects onto the same cycle view.
#guard cycleOf reg == cyc

-- And therefore the SAME `divResult` call gives the SAME answer on both,
-- which is the whole point of stating rung A through `cycleOf`.
#guard (divResult cyc "ready_o" "result_o").map LVec.toNat == some 7
#guard (divResult reg "ready_o" "result_o").map LVec.toNat == some 7

-- The first asserted cycle wins, not the last.
#guard (divResult cyc "ready_o" "result_o") != (some (bitv 9 8))

-- No trigger anywhere: no observation, rather than a default.
#guard divResult ([stX] : List SvState) "ready_o" "result_o" == none

-- An unknown trigger is NOT a trigger.
#guard divResult ([[("ready_o", LVec.xVec 1), ("result_o", bitv 7 8)]] : List SvState)
    "ready_o" "result_o" == none

-- The real CV32E40P handshake names, on both trace types — the exact call
-- rung A will make (`cv32e40p_alu_div`: OutVld_SO / Res_DO).
private def cvCyc : List SvState :=
  [[("OutVld_SO", bitv 0 1), ("Res_DO", bitv 0 32)],
   [("OutVld_SO", bitv 1 1), ("Res_DO", bitv 5 32)]]
private def cvReg : RegionTrace :=
  [⟨0, [], cvCyc[0]!⟩, ⟨10, cvCyc[0]!, cvCyc[1]!⟩]

#guard (divResult cvCyc "OutVld_SO" "Res_DO").map LVec.toNat == some 5
#guard (divResult cvReg "OutVld_SO" "Res_DO").map LVec.toNat == some 5

-- The oracle embedding is transparent.
#guard (ρ_src.choose 0 Region.active [0, 1, 2]) == [0, 1, 2]
#guard (ρ_rev.choose 0 Region.active [0, 1, 2]) == [2, 1, 0]

-- A region-local witness reorders in its region only.
#guard ((RegionOracle.revIn Region.active).choose 0 Region.active [0, 1, 2]) == [2, 1, 0]
#guard ((RegionOracle.revIn Region.active).choose 0 Region.nba [0, 1, 2]) == [0, 1, 2]

-- Region bookkeeping.
#guard Region.all.length == 15
#guard (Region.all.filter Region.isPLI).length == 6
#guard Region.postponed.isReadOnly
#guard !Region.active.isReadOnly

end Guards

end LeanModels.Sv
