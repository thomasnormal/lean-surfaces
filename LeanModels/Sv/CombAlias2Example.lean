import LeanModels.Sv.CombAlias2Sound
import LeanModels.Sv.Comb2ProcExample

/-!
# The alias guard on the proof API's designs (WP4 round 6, lane B)

`Comb2ProcExample.lean` hand-builds the `always_comb` designs the proof API
is about (`faDesign`, `muxDesign`, `latchDesign`, `decDesign`, and the
adder/subtractor `asDesign N` at EVERY width). The alias guard
(`CombAlias2.lean`) sits beside `name.sem`, so none of their recorded
theorems mentions it; this file discharges it for them anyway — the proof
API's designs are never refused by the guard — and pins the two shapes it
exists for on a hand-built twin of the SV fixtures.

* **No continuous assignment, no alias** (`Design2.aliasGuard_of_noAssign`):
  each design below has one `always_comb` process and nothing else, so the
  guard is the identity on it (`fa_aliasGuard`, …, `as_aliasGuard N` for
  every `N`).
* **`assign w = t; always_comb begin y = w; t = a; end` is refused**
  (`alias_guard`: `acg_alias_assign`'s design, the walk finds the read of `w`
  on all of its bits), **`t = a; y = w;` is admitted** (`wr_admits`, the
  fixture `acg_alias_wr`), **and so is the copy through a separate
  `always_comb`** (`copy_aliasGuard`, `acg_alias_copy`).

(This import also keeps `CombAlias2Sound` under the default `Examples`
build, through the `agree.lean` files of the `always_comb` fixtures that
import this module.)
-/

namespace LeanModels.Sv

namespace CombAlias2Example

open Comb2ProcExample CombGuard

/-! ## The proof API's designs have no continuous assignment -/

theorem fa_aliasGuard : faDesign.aliasGuard = faDesign :=
  Design2.aliasGuard_of_noAssign (by simp [faDesign])

theorem mux_aliasGuard : muxDesign.aliasGuard = muxDesign :=
  Design2.aliasGuard_of_noAssign (by simp [muxDesign])

theorem latch_aliasGuard : latchDesign.aliasGuard = latchDesign :=
  Design2.aliasGuard_of_noAssign (by simp [latchDesign])

theorem dec_aliasGuard : decDesign.aliasGuard = decDesign :=
  Design2.aliasGuard_of_noAssign (by simp [decDesign])

/-- The adder/subtractor at EVERY width. -/
theorem as_aliasGuard (N : Nat) : (asDesign N).aliasGuard = asDesign N :=
  Design2.aliasGuard_of_noAssign (by simp [asDesign])

/-! ## The shapes the guard exists for -/

/-- `acg_alias_assign`: `assign w = t; always_comb begin y = w; t = a; end`. -/
def aliasBody : Stmt2 := .block #[
  .blockingAssign (.ident "y") (.ident "w"),
  .blockingAssign (.ident "t") (.ident "a")]

def aliasDesign : Design2 where
  name := "acg_alias_assign"
  decls := #[
    { name := "a", width := 2, isInput := true },
    { name := "y", width := 2, isOutput := true },
    { name := "t", width := 2 },
    { name := "w", width := 2 }]
  processes := #[.assign (.ident "w") (.ident "t"), .alwaysComb aliasBody]

/-- The self-read guard admits it (the block reads no bit it writes) … -/
theorem alias_selfread_admits : aliasBody.combAdmits aliasDesign.combWd = true := by decide

/-- … the alias guard refuses it: the read of `w` (a copy of `t`) comes before
the write of `t`, on all of `w`. -/
theorem alias_guard :
    aliasBody.aliasViol aliasDesign.combWd
      (aliasFlows aliasDesign.combWd aliasDesign.processes.toList) [] = some ("w", 0, 2) := by
  decide

/-- `t = a; y = w;` — write then read — is admitted. -/
def wrBody : Stmt2 := .block #[
  .blockingAssign (.ident "t") (.ident "a"),
  .blockingAssign (.ident "y") (.ident "w")]

def wrDesign : Design2 := { aliasDesign with name := "acg_alias_wr", processes :=
  #[.assign (.ident "w") (.ident "t"), .alwaysComb wrBody] }

theorem wr_admits :
    wrBody.aliasAdmits wrDesign.combWd (aliasFlows wrDesign.combWd wrDesign.processes.toList)
      = true := by decide

/-- … and so is the guard on the design: it is its own guard. -/
theorem wr_aliasGuard : wrDesign.aliasGuard = wrDesign :=
  Design2.aliasGuard_of_admits fun b hb => by
    simp [wrDesign] at hb
    subst hb
    exact Option.isNone_iff_eq_none.mp wr_admits

/-- The copy through a SEPARATE `always_comb` is no continuous assignment:
admitted. -/
def copyDesign : Design2 := { aliasDesign with name := "acg_alias_copy", processes :=
  #[.alwaysComb (.blockingAssign (.ident "w") (.ident "t")), .alwaysComb aliasBody] }

theorem copy_aliasGuard : copyDesign.aliasGuard = copyDesign :=
  Design2.aliasGuard_of_admits fun b hb => by
    simp [copyDesign] at hb
    rcases hb with rfl | rfl <;> decide

/-- The alias refusal is loud: the guard puts the `AlwaysComb:alias-read`
process in place of the block (the analogue of `Comb2ProcExample.rbw_guard`). -/
theorem alias_refused :
    aliasGuardProc aliasDesign.name aliasDesign.combWd
        (aliasFlows aliasDesign.combWd aliasDesign.processes.toList) (.alwaysComb aliasBody) =
      .unsupported "AlwaysComb:alias-read"
        (aliasMsg aliasDesign.name
          (aliasSource aliasDesign.combWd (aliasFlows aliasDesign.combWd aliasDesign.processes.toList)
            aliasBody ("w", 0, 2)) ("w", 0, 2)) :=
  aliasGuardProc_of_viol alias_guard

/-! ## Axiom pins

The `#guard_msgs` wrappers make the build fail if any of these drifts. -/

/--
info: 'LeanModels.Sv.CombAlias2Example.as_aliasGuard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms as_aliasGuard

/--
info: 'LeanModels.Sv.CombAlias2Example.alias_guard' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms alias_guard

/--
info: 'LeanModels.Sv.CombAlias2Example.alias_refused' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms alias_refused

/--
info: 'LeanModels.Sv.CombAlias2Example.wr_aliasGuard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wr_aliasGuard

/--
info: 'LeanModels.Sv.CombAlias2Example.fa_aliasGuard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fa_aliasGuard

/--
info: 'LeanModels.Sv.CombAlias2Example.mux_aliasGuard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mux_aliasGuard

/--
info: 'LeanModels.Sv.CombAlias2Example.latch_aliasGuard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms latch_aliasGuard

/--
info: 'LeanModels.Sv.CombAlias2Example.dec_aliasGuard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dec_aliasGuard

/--
info: 'LeanModels.Sv.CombAlias2Example.alias_selfread_admits' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms alias_selfread_admits

/--
info: 'LeanModels.Sv.CombAlias2Example.wr_admits' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms wr_admits

/--
info: 'LeanModels.Sv.CombAlias2Example.copy_aliasGuard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms copy_aliasGuard

end CombAlias2Example

end LeanModels.Sv
