import LeanModels.Sv.CombGuard2

/-!
# The always_comb alias guard core

This module contains the source-independent alias-flow walk and the flat
`Design2.aliasGuard`. It deliberately imports no hierarchy or parameter
instantiation module, so the guard can run inside every parameter-point
semantic instantiation without creating an import cycle.
-/

namespace LeanModels.Sv

open CombGuard

namespace CombGuard

/-! ## Continuous flows and their fan-out -/

/-- One continuous assignment as a flow: the windows its evaluation reads
(right-hand side and the target's run-time index expressions), then the
windows it may write. -/
abbrev AFlow := List BWin × List BWin

/-- The window lists share a bit (the intersection of some pair is
non-empty). -/
def touches (F R : List BWin) : Bool :=
  R.any fun r => F.any fun f => (r.inter f).2.2 != 0

/-- The assignments of `rem` that read a bit of `S`. -/
def hitsOf (S : List BWin) (rem : List AFlow) : List AFlow :=
  rem.filter fun fl => touches S fl.1

/-- The assignments of `rem` that read no bit of `S`. -/
def missOf (S : List BWin) (rem : List AFlow) : List AFlow :=
  rem.filter fun fl => !touches S fl.1

/-- The reached windows: `acc` so far; each round fires the assignments of
`rem` that read a bit of `A ++ acc` (each fires once and leaves `rem`) and
appends their write windows; no assignment left to fire, or no fuel, ends
it. With the fuel `rem.length` every assignment gets its chance
(`fanAux_closed`). -/
def fanAux : Nat → List AFlow → List BWin → List BWin → List BWin
  | 0, _, _, acc => acc
  | n + 1, rem, A, acc =>
      let hit := hitsOf (A ++ acc) rem
      if hit.isEmpty then acc
      else fanAux n (missOf (A ++ acc) rem) A (acc ++ hit.flatMap (·.2))

/-- **The fan-out of `A` through the continuous assignments `fl`**: the
write windows of every assignment reachable from `A` by at least one hop
(`A` itself is not in it unless a loop leads back). -/
def fanOut (fl : List AFlow) (A : List BWin) : List BWin := fanAux fl.length fl A []

/-- The alias check of one read set against one written-after set: the
first read window that overlaps a window downstream of `X`. -/
def aliasChk (fl : List AFlow) (X R : List BWin) : Option BWin :=
  readsViol [] (fanOut fl X) R

end CombGuard

/-- The flow of a process: an `assign` reads its right-hand side and its
target's index expressions and may write its target; no other process is a
continuous assignment. -/
def Process2.aflow (wd : String → Option Nat) : Process2 → List AFlow
  | .assign t e => [(e.rdW wd ++ t.rdW wd, t.mayW wd)]
  | _ => []

/-- The continuous flows of a process list (after flattening these include
the port connections). -/
def aliasFlows (wd : String → Option Nat) (ps : List Process2) : List AFlow :=
  ps.flatMap (Process2.aflow wd)

/-! ## The walk -/

mutual
/-- **The first alias-read violation** of statement `s` (`none`: none),
given the windows `A` some path may write after `s`. The shape of
`Stmt2.combViol` with the must-write set dropped and every written set
replaced by its fan-out; an assignment reads its right-hand side and its
target's index expressions BEFORE it writes its target. -/
def Stmt2.aliasViol (wd : String → Option Nat) (fl : List AFlow) (A : List BWin) :
    Stmt2 → Option BWin
  | .blockingAssign t e => aliasChk fl (t.mayW wd ++ A) (e.rdW wd ++ t.rdW wd)
  | .nbaAssign t e => aliasChk fl A (e.rdW wd ++ t.rdW wd)
  | .ifStmt c a b =>
      aliasChk fl (a.mayW wd ++ Stmt2.optMayW wd b ++ A) (c.rdW wd) <|>
        a.aliasViol wd fl A <|> Stmt2.optAliasViol wd fl A b
  | .block ss => Stmt2.listAliasViol wd fl A ss.toList
  | .caseStmt subj its d _ _ =>
      aliasChk fl (CaseItem2.listMayW wd its.toList ++ Stmt2.optMayW wd d ++ A) (subj.rdW wd) <|>
        CaseItem2.listAliasViol wd fl A (Stmt2.optMayW wd d) (Stmt2.optAliasViol wd fl A d)
          its.toList
  | .unsupported _ _ => none
termination_by structural s => s

/-- `Stmt2.aliasViol` of an optional statement. -/
def Stmt2.optAliasViol (wd : String → Option Nat) (fl : List AFlow) (A : List BWin) :
    Option Stmt2 → Option BWin
  | none => none
  | some s => s.aliasViol wd fl A
termination_by structural o => o

/-- A sequence: each statement sees the may-writes of the ones after it. -/
def Stmt2.listAliasViol (wd : String → Option Nat) (fl : List AFlow) (A : List BWin) :
    List Stmt2 → Option BWin
  | [] => none
  | s :: ss =>
      s.aliasViol wd fl (Stmt2.listMayW wd ss ++ A) <|> Stmt2.listAliasViol wd fl A ss
termination_by structural ss => ss

/-- The arms of a `case` (`dA`: the default's may-writes, `dV`: the
default's violation), as `CaseItem2.listCombViol`. -/
def CaseItem2.listAliasViol (wd : String → Option Nat) (fl : List AFlow) (A dA : List BWin)
    (dV : Option BWin) : List CaseItem2 → Option BWin
  | [] => dV
  | .mk pats body :: rest =>
      aliasChk fl (body.mayW wd ++ CaseItem2.listMayW wd rest ++ dA ++ A)
          (Expr2.listRdW wd pats.toList) <|>
        body.aliasViol wd fl A <|> CaseItem2.listAliasViol wd fl A dA dV rest
termination_by structural its => its
end

/-! ## The guard -/

/-- The walk from an empty written-after set finds no alias read. -/
def Stmt2.aliasAdmits (wd : String → Option Nat) (fl : List AFlow) (body : Stmt2) : Bool :=
  (body.aliasViol wd fl []).isNone

/-- The first written window `x` of the body whose fan-out overlaps the
violating window `W` (the message names its signal). -/
def aliasSource (wd : String → Option Nat) (fl : List AFlow) (body : Stmt2) (W : BWin) :
    Option String :=
  (body.mayW wd).findSome? fun x => if touches (fanOut fl [x]) [W] then some x.1 else none

/-- The refusal message for a violating window `W` of the `always_comb` of
module `mname`. A signal of a flattened instance (`u.w`) is named with its
instance. -/
def aliasMsg (mname : String) (src : Option String) (W : BWin) : String :=
  let bits := if W.2.2 = 1 then s!"bit [{W.2.1}]" else s!"bits [{W.2.1 + W.2.2 - 1}:{W.2.1}]"
  let parts := W.1.splitOn "."
  let loc := parts.getLast?.getD W.1
  let path := ".".intercalate parts.dropLast
  let inst := if parts.length > 1 then
      s!" (signal '{loc}' of instance '{path}', flattened name '{W.1}')"
    else ""
  let from_ := match src with
    | some s => s!"'{s}'"
    | none => "a variable"
  s!"always_comb block of module '{mname}' reads {bits} of '{W.1}'{inst}, a continuous copy (an `assign`, a net or a port connection, possibly through a chain of them) of {from_}, which the block writes later on that path (or in the very statement that reads the copy): IEEE 1800-2023 §9.2.2.2.1 puts the copy in the block's implicit sensitivity list, but §4.7/§4.8 let a simulator update the copy inside the block's own run, where the wake-up is lost (Icarus 12 keeps the previous value in the read), or defer the update and re-run the block (Xcelium 24.03, Verilator 5.042 and the settle semantics): no answer is safe, so the block is refused (read the copy after the last write of its source, or copy in a separate always_comb)"

/-- **The guard on one process** (`mname`: the design's name): an
`always_comb` whose body the walk refuses becomes a loud
`AlwaysComb:alias-read` process; every other process is unchanged. -/
def aliasGuardProc (mname : String) (wd : String → Option Nat) (fl : List AFlow) :
    Process2 → Process2
  | .alwaysComb b =>
      match b.aliasViol wd fl [] with
      | some W => .unsupported "AlwaysComb:alias-read" (aliasMsg mname (aliasSource wd fl b W) W)
      | none => .alwaysComb b
  | p => p

/-- **The alias guard on a flat design** (instance-free or flattened): the
design's declared widths (`Design2.combWd`) and continuous flows
(`aliasFlows`), then `aliasGuardProc` on every process. The declarations,
the name and the order of the processes are kept. -/
def Design2.aliasGuard (m : Design2) : Design2 :=
  let wd := m.combWd
  let fl := aliasFlows wd m.processes.toList
  { m with processes := m.processes.map (aliasGuardProc m.name wd fl) }

/-- The first `AlwaysComb:alias-read` message of the guarded design, if
any. -/
def Design2.aliasReport (m : Design2) : Option String :=
  m.aliasGuard.processes.toList.findSome? fun p =>
    match p with
    | .unsupported "AlwaysComb:alias-read" msg => some msg
    | _ => none

/-- Every `always_comb` of the design passes. -/
def Design2.aliasAdmits (m : Design2) : Bool := m.aliasReport.isNone

/-! ## Lemmas the examples use -/

theorem aliasGuardProc_of_admits {mname : String} {wd : String → Option Nat} {fl : List AFlow}
    {body : Stmt2} (h : body.aliasViol wd fl [] = none) :
    aliasGuardProc mname wd fl (.alwaysComb body) = .alwaysComb body := by
  simp [aliasGuardProc, h]

theorem aliasGuardProc_of_viol {mname : String} {wd : String → Option Nat} {fl : List AFlow}
    {body : Stmt2} {W : BWin} (h : body.aliasViol wd fl [] = some W) :
    aliasGuardProc mname wd fl (.alwaysComb body) =
      .unsupported "AlwaysComb:alias-read" (aliasMsg mname (aliasSource wd fl body W) W) := by
  simp [aliasGuardProc, h]

/-- Only `always_comb` processes are touched. -/
theorem aliasGuardProc_of_ne {mname : String} {wd : String → Option Nat} {fl : List AFlow}
    {p : Process2} (h : ∀ b, p ≠ .alwaysComb b) : aliasGuardProc mname wd fl p = p := by
  cases p <;> first | rfl | exact absurd rfl (h _)

@[simp] theorem Design2.aliasGuard_name (m : Design2) : m.aliasGuard.name = m.name := rfl

@[simp] theorem Design2.aliasGuard_decls (m : Design2) : m.aliasGuard.decls = m.decls := rfl

theorem Design2.aliasGuard_processes (m : Design2) :
    m.aliasGuard.processes.toList =
      m.processes.toList.map (aliasGuardProc m.name m.combWd
        (aliasFlows m.combWd m.processes.toList)) := by
  simp [Design2.aliasGuard]

private theorem array_map_self {α : Type} (f : α → α) (ps : Array α)
    (h : ∀ p ∈ ps.toList, f p = p) : ps.map f = ps := by
  apply Array.ext'
  rw [Array.toList_map]
  exact (List.map_congr_left (g := id) h).trans (List.map_id _)

/-- A design without `always_comb` is its own guard — every ∀-N family the
repository proves a theorem about (`ripple_add`, `mul2d`, `partsel`,
`ripple_fa`) is continuous-only. -/
theorem Design2.aliasGuard_of_noComb {m : Design2}
    (h : ∀ p ∈ m.processes.toList, ∀ b, p ≠ .alwaysComb b) : m.aliasGuard = m := by
  have key : m.processes.map (aliasGuardProc m.name m.combWd
      (aliasFlows m.combWd m.processes.toList)) = m.processes :=
    array_map_self _ _ (fun p hp => aliasGuardProc_of_ne (h p hp))
  simp only [Design2.aliasGuard]
  rw [key]

/-- A design with no continuous assignments has no alias flow. -/
theorem aliasFlows_nil_of_noAssign {wd : String → Option Nat} {ps : List Process2}
    (h : ∀ p ∈ ps, ∀ t e, p ≠ .assign t e) : aliasFlows wd ps = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [aliasFlows, List.flatMap_cons]
      have hp : Process2.aflow wd p = [] := by
        cases p with
        | assign t e => exact (h (.assign t e) (by simp) t e).elim rfl
        | _ => rfl
      rw [hp]
      simp only [List.nil_append]
      change aliasFlows wd ps = []
      exact ih (fun q hq => h q (by simp [hq]))

/-- A design every `always_comb` of which the walk admits is its own guard. -/
theorem Design2.aliasGuard_of_admits {m : Design2}
    (h : ∀ b, .alwaysComb b ∈ m.processes.toList →
      b.aliasViol m.combWd (aliasFlows m.combWd m.processes.toList) [] = none) :
    m.aliasGuard = m := by
  have key : m.processes.map (aliasGuardProc m.name m.combWd
      (aliasFlows m.combWd m.processes.toList)) = m.processes := by
    apply array_map_self
    intro p hp
    cases p with
    | alwaysComb b => exact aliasGuardProc_of_admits (h b hp)
    | _ => rfl
  simp only [Design2.aliasGuard]
  rw [key]


end LeanModels.Sv
