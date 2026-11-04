import LeanModels.Sv.World

/-!
# R1 inch 4a — the `SvM` primitive layer

The operations `slotStep` is built from, written against the family monad
rather than against hand-threaded state. This is where §9.0's
`0/N semantics on SvM` starts counting.

**Why primitives before the region loop.** `docs/family-architecture.md`
§4 prices a tier's per-language cost as *the World type, the error type,
the primitive step functions, and their laws* — the loop on top is where
`mvcgen` and the shared machinery do their work, and it can only be
written once the primitives exist and are pinned. So this file is the
whole of the per-language cost, and the region ladder that follows it is
supposed to be cheap.

**The load-bearing claim is `finish_preserves_out`.** This tier has
asserted in prose, repeatedly, that `$finish` belongs in `ρ` rather than
in `Loud` because `SvWorld.out` holds the `PASS`/`FAIL` line and a `Loud`
halt would discard it. That is a claim about the layer ORDER —
`ExceptT ρ` outside `StateT W` — and it is checkable rather than
believable. Below it is a `#guard`.
-/

namespace LeanModels.Sv

open SelfCheck

set_option autoImplicit false

/-! ## Running an `SvM` -/

/-- Run an `SvM` action from a starting world.

The shape is the layer order made visible: `ExceptT ρ (StateT W Halt)`
unfolds to `W → Halt (Except ρ α × W)`, so a `ρ`-raise returns **with the
world**, while a `Loud` halt returns no world at all. -/
def SvM.exec {α : Type} (m : SvM α) (w : SvWorld) :
    HaltWith SvClause Unit (Except Finish α × SvWorld) :=
  StateT.run (ExceptT.run m) w

/-! ## Signal primitives -/

/-- Read a declared signal. An undeclared name is a loud refusal, never a
default value — the M0 interpreter's rule, carried onto the substrate. -/
def readSig (n : String) : SvM LVec := do
  let w ← get
  match SvState.lookup w.signals n with
  | some v => pure v
  | none => refuseSv .outOfTier ⟨"6.5"⟩ s!"read of undeclared signal '{n}'"

/-- Write a signal immediately (the blocking-assignment effect). -/
def writeSig (n : String) (v : LVec) : SvM Unit :=
  modify fun w => { w with signals := SvState.set w.signals n v }

/-! ## Nonblocking assignment — the Active/NBA split -/

/-- Queue a nonblocking update. Evaluated in Active, applied in NBA: this
is the write half, and it does NOT touch `signals`. -/
def pushNba (n : String) (v : LVec) : SvM Unit :=
  modify fun w => { w with nba := w.nba ++ [(n, v)] }

/-- Apply the queued nonblocking updates in order and clear the queue.
Last write to a name wins, which is IEEE 1800's rule and the reason the
queue is ordered rather than a map. -/
def applyNba : SvM Unit :=
  modify fun w =>
    { w with signals := w.nba.foldl (fun st (n, v) => SvState.set st n v) w.signals
           , nba := [] }

/-! ## Output and termination -/

/-- `$display`/`$write` text. For most of the conformance corpus this is
the verdict, which is why the next definition must not discard it. -/
def emit (s : String) : SvM Unit :=
  modify fun w => { w with out := w.out.emit s }

/-- `$finish` / `$stop`: raise `ρ`. State-PRESERVING by construction —
see `finish_preserves_out`. -/
def finishSim {α : Type} (f : Finish) : SvM α := throw f

/-! ## Region and time -/

/-- Move to a region. The ORDER of regions is fixed by IEEE 1800 §4.4 and
is not a schedule choice; only the order of processes WITHIN a region is,
and that is the oracle's business, not the world's. -/
def setRegion (r : Region) : SvM Unit :=
  modify fun w => { w with curRegion := r }

/-- Advance simulation time. -/
def advanceTime (d : Nat) : SvM Unit :=
  modify fun w => { w with time := w.time + d }

/-! ## The laws, as guards

Each pins one primitive's contract. They are `#guard`s rather than
theorems on purpose at this inch: they are facts about CONCRETE runs, and
the general statements belong with the region loop that will quantify
over them. -/

section Guards

private def w0 : SvWorld := { signals := [("a", LVec.ofNat 4 5)] }

private def okOf {α : Type} (r : HaltWith SvClause Unit (Except Finish α × SvWorld)) :
    Option SvWorld :=
  match r with
  | .ok (_, w) => some w
  | .error _ => none

private def valOf (r : HaltWith SvClause Unit (Except Finish LVec × SvWorld)) : Option Nat :=
  match r with
  | .ok (.ok v, _) => some v.toNat
  | _ => none

-- read sees what write wrote
#guard valOf (SvM.exec (do writeSig "a" (LVec.ofNat 4 9); readSig "a") w0) == some 9

-- an undeclared read REFUSES rather than defaulting
#guard (okOf (SvM.exec (readSig "nope") w0)).isNone

-- a nonblocking write is NOT visible before the commit ...
#guard valOf (SvM.exec (do pushNba "a" (LVec.ofNat 4 9); readSig "a") w0) == some 5

-- ... and IS visible after it
#guard valOf (SvM.exec (do pushNba "a" (LVec.ofNat 4 9); applyNba; readSig "a") w0) == some 9

-- last write to a name wins, and the queue is emptied
#guard valOf (SvM.exec
    (do pushNba "a" (LVec.ofNat 4 1); pushNba "a" (LVec.ofNat 4 7); applyNba; readSig "a") w0)
  == some 7
#guard ((okOf (SvM.exec (do pushNba "a" (LVec.ofNat 4 1); applyNba) w0)).map
          (fun w => w.nba.length)) == some 0

/-! **THE LAYER-ORDER CLAIM, CHECKED.** `$finish` raises `ρ` and the world
survives with its output intact. If `ExceptT` and `StateT` were nested the
other way the state would be discarded here and this guard would read
`none` — which is exactly the failure the family document corrected by
`rfl`, and exactly what would have silently thrown away the `PASS` line. -/
#guard ((okOf (SvM.exec (do emit "PASS"; finishSim .finish : SvM Unit) w0)).map
          (fun w => w.out.flush)) == some ["PASS"]

-- and the raise really is a `ρ`, not a `Loud`: the run still `.ok`s at the base
#guard (okOf (SvM.exec (finishSim .stop : SvM Unit) w0)).isSome

-- region and time move
#guard ((okOf (SvM.exec (setRegion .nba) w0)).map (fun w => w.curRegion == Region.nba)) == some true
#guard ((okOf (SvM.exec (advanceTime 10) w0)).map (fun w => w.time)) == some 10

end Guards

end LeanModels.Sv
