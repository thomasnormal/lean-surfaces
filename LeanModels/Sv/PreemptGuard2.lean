import LeanModels.Sv.CombAliasCore

/-!
# The preemption profile guard

`Sem2` deliberately executes one ready process activation to completion.  IEEE
1800-2023 §4.7 also permits a simulator to suspend a process while evaluating
a statement.  This module supplies the conservative profile boundary: it
admits a design when no *partial* write of one process can be observed by
another process.  A single assignment is an atomic statement for this guard,
and an NBA-only process publishes only at the NBA commit, so ordinary
clocked flops and settled one-assignment combinational stages remain admitted.
Blocks with several blocking writes retain all of their may-write windows;
cross-process reads or competing writes touching those windows are reported
loudly rather than assigned a scheduler choice that E does not model.
-/

namespace LeanModels.Sv

open CombGuard

/-! ## Access summaries -/

mutual
  /-- Reads of one procedural statement, including conditions and case labels. -/
  def Stmt2.preemptReads (wd : String → Option Nat) : Stmt2 → List BWin
    | .blockingAssign t e | .nbaAssign t e => e.rdW wd ++ t.rdW wd
    | .ifStmt c t e =>
        c.rdW wd ++ t.preemptReads wd ++ Stmt2.optPreemptReads wd e
    | .block ss => Stmt2.listPreemptReads wd ss.toList
    | .caseStmt subj items dflt _ _ =>
        subj.rdW wd ++ CaseItem2.listPreemptReads wd items.toList ++
          Stmt2.optPreemptReads wd dflt
    | .unsupported _ _ => []
    termination_by structural s => s

  def Stmt2.optPreemptReads (wd : String → Option Nat) : Option Stmt2 → List BWin
    | none => []
    | some s => s.preemptReads wd
    termination_by structural o => o

  def Stmt2.listPreemptReads (wd : String → Option Nat) : List Stmt2 → List BWin
    | [] => []
    | s :: ss => s.preemptReads wd ++ Stmt2.listPreemptReads wd ss
    termination_by structural ss => ss

  def CaseItem2.preemptReads (wd : String → Option Nat) : CaseItem2 → List BWin
    | .mk pats body =>
        pats.toList.flatMap (Expr2.rdW wd) ++ body.preemptReads wd
    termination_by structural it => it

  def CaseItem2.listPreemptReads (wd : String → Option Nat) : List CaseItem2 → List BWin
    | [] => []
    | it :: rest => it.preemptReads wd ++ CaseItem2.listPreemptReads wd rest
    termination_by structural its => its
end

abbrev ProcessAccess := List BWin × List BWin

/-! A write is observable *during* a process only after an earlier blocking
statement has completed.  NBA statements do not publish until the commit
region, and one blocking assignment has no intermediate store. -/

mutual
  def Stmt2.allNba (s : Stmt2) : Bool :=
    match s with
    | .nbaAssign _ _ => true
    | .blockingAssign _ _ | .unsupported _ _ => false
    | .ifStmt _ t e => t.allNba && Stmt2.optAllNba e
    | .block ss => Stmt2.listAllNba ss.toList
    | .caseStmt _ items d _ _ => CaseItem2.listAllNba items.toList && Stmt2.optAllNba d

  def Stmt2.optAllNba : Option Stmt2 → Bool
    | none => true
    | some s => s.allNba

  def Stmt2.listAllNba : List Stmt2 → Bool
    | [] => true
    | s :: ss => s.allNba && Stmt2.listAllNba ss

  def CaseItem2.listAllNba : List CaseItem2 → Bool
    | [] => true
    | .mk _ body :: rest => body.allNba && CaseItem2.listAllNba rest

  def Stmt2.preemptWrites (wd : String → Option Nat) : Stmt2 → List BWin
    | .blockingAssign _ _ | .nbaAssign _ _ => []
    | .ifStmt _ t e => t.preemptWrites wd ++ Stmt2.optPreemptWrites wd e
    | .block ss =>
        let xs := Stmt2.listMayW wd ss.toList
        if Stmt2.listAllNba ss.toList || xs.length <= 1 then [] else xs
    | .caseStmt _ items dflt _ _ =>
        CaseItem2.listPreemptWrites wd items.toList ++ Stmt2.optPreemptWrites wd dflt
    | .unsupported _ _ => []
    termination_by structural s => s

  def Stmt2.optPreemptWrites (wd : String → Option Nat) : Option Stmt2 → List BWin
    | none => []
    | some s => s.preemptWrites wd
    termination_by structural o => o

  def Stmt2.listPreemptWrites (wd : String → Option Nat) : List Stmt2 → List BWin
    | [] => []
    | s :: ss => s.preemptWrites wd ++ Stmt2.listPreemptWrites wd ss
    termination_by structural ss => ss

  def CaseItem2.preemptWrites (wd : String → Option Nat) : CaseItem2 → List BWin
    | .mk _ body => body.preemptWrites wd
    termination_by structural it => it

  def CaseItem2.listPreemptWrites (wd : String → Option Nat) : List CaseItem2 → List BWin
    | [] => []
    | it :: rest => it.preemptWrites wd ++ CaseItem2.listPreemptWrites wd rest
    termination_by structural its => its
end

/-- All reads and may-writes of one process at the instantiated widths. -/
def Process2.preemptAccess (wd : String → Option Nat) : Process2 → ProcessAccess
  | .assign t e => (e.rdW wd ++ t.rdW wd, [])
  | .alwaysComb b | .alwaysFF _ b | .alwaysPlain _ b | .alwaysFFR _ _ b _ =>
      (b.preemptReads wd, b.preemptWrites wd)
  | .unsupported _ _ => ([], [])

/-- A conflict means that a process can read a bit another process writes, or
that two processes can write the same bit.  It is intentionally conservative:
the profile refuses before choosing a simulator's suspension point. -/
def ProcessAccess.conflicts (a b : ProcessAccess) : Bool :=
  touches a.2 b.1 || touches b.2 a.1 || touches a.2 b.2

def firstPreemptConflict (ps : List ProcessAccess) (i : Nat) : Option (Nat × Nat) :=
  match ps with
  | [] => none
  | a :: rest =>
      match rest.findIdx? (fun b => a.conflicts b) with
      | some j => some (i, i + j + 1)
      | none => firstPreemptConflict rest (i + 1)

/-- The first refusal for the preemptive profile, if any. -/
def Design2.preemptionReport (m : Design2) : Option (String × String) :=
  let wd := m.combWd
  let accesses := m.processes.toList.map (Process2.preemptAccess wd)
  match firstPreemptConflict accesses 0 with
  | none => none
  | some (i, j) =>
      some ("Schedule:preemptive",
        s!"processes {i} and {j} may observe an intermediate write under IEEE 1800-2023 §4.7; the preemptive profile requires disjoint cross-process reads/writes")

/-- Turn a preemption-profile violation into the normal loud process node. -/
def Design2.preemptionGuard (m : Design2) : Design2 :=
  match m.preemptionReport with
  | none => m
  | some (kind, msg) =>
      { m with processes := m.processes.push (.unsupported kind msg) }

def Design2.preemptionAdmits (m : Design2) : Bool := m.preemptionReport.isNone

/-! ## Small source-shaped guards -/

private def indep : Design2 :=
  { name := "preempt_indep"
    decls := #[
      { name := "a", width := 1, isInput := true },
      { name := "b", width := 1, isInput := true },
      { name := "q", width := 1, isOutput := true },
      { name := "r", width := 1, isOutput := true }]
    processes := #[
      .alwaysFF "clk" (.nbaAssign (.ident "q") (.ident "a")),
      .alwaysFF "clk" (.nbaAssign (.ident "r") (.ident "b"))] }

private def dep : Design2 :=
  { indep with
    name := "preempt_dep"
    processes := #[
      .alwaysComb (.block #[
        .blockingAssign (.ident "q") (.ident "a"),
        .blockingAssign (.ident "r") (.ident "q")]),
      .alwaysFF "clk" (.nbaAssign (.ident "r") (.ident "q"))] }

#guard indep.preemptionReport == none
#guard dep.preemptionAdmits == false
#guard match dep.preemptionReport with
  | some ("Schedule:preemptive", _) => true
  | _ => false
#guard dep.preemptionGuard.processes.toList.any fun p =>
  match p with | .unsupported "Schedule:preemptive" _ => true | _ => false

end LeanModels.Sv
