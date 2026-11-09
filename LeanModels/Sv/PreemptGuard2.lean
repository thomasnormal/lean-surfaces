import LeanModels.Sv.CombAliasCore

/-!
# The preemption profile guard

`Sem2` deliberately executes one ready process activation to completion.  IEEE
1800-2023 §4.7 also permits a simulator to suspend a process while evaluating
a statement.  This module supplies the conservative route boundary for that
freedom: a design is admitted only when a process cannot expose a partial
write to another process.  A single continuous assignment and an edge process
whose body is NBA-only publish their writes after their evaluation, so they do
not expose an intermediate value; conflicts involving a blocking or
multi-write body are reported loudly.  Designs outside the condition are
reported loudly; this does not pretend to implement the missing scheduler
choice point.

The guard is beside `name.sem`, like the clock and alias guards.  The route
entry points use it by default; the low-level evaluators remain source-shaped
so proof statements can still name their exact AST and the route can refuse
before execution.
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

/-! A process whose writes are not observable until its activation has
finished.  This is the small region fact that lets NBA-only sequential blocks
and one-shot continuous assignments retain the cycle view under §4.7. -/

mutual
  def Stmt2.preemptNBAOnly : Stmt2 → Bool
    | .nbaAssign _ _ => true
    | .blockingAssign _ _ => false
    | .ifStmt _ t e => Stmt2.preemptNBAOnly t && Stmt2.optPreemptNBAOnly e
    | .block ss => Stmt2.listPreemptNBAOnly ss.toList
    | .caseStmt _ items dflt _ _ =>
        CaseItem2.listPreemptNBAOnly items.toList && Stmt2.optPreemptNBAOnly dflt
    | .unsupported _ _ => false
    termination_by structural s => s

  def Stmt2.optPreemptNBAOnly : Option Stmt2 → Bool
    | none => true
    | some s => Stmt2.preemptNBAOnly s
    termination_by structural o => o

  def Stmt2.listPreemptNBAOnly : List Stmt2 → Bool
    | [] => true
    | s :: rest => Stmt2.preemptNBAOnly s && Stmt2.listPreemptNBAOnly rest
    termination_by structural ss => ss

  def CaseItem2.preemptNBAOnly : CaseItem2 → Bool
    | .mk _ body => Stmt2.preemptNBAOnly body
    termination_by structural it => it

  def CaseItem2.listPreemptNBAOnly : List CaseItem2 → Bool
    | [] => true
    | item :: rest =>
        CaseItem2.preemptNBAOnly item && CaseItem2.listPreemptNBAOnly rest
    termination_by structural items => items
end

def Process2.preemptAtomic : Process2 → Bool
  | .assign _ _ => true
  | .alwaysFF _ body | .alwaysPlain _ body | .alwaysFFR _ _ body _ =>
      Stmt2.preemptNBAOnly body
  | _ => false

/-- All reads and may-writes of one process at the instantiated widths. -/
def Process2.preemptAccess (wd : String → Option Nat) : Process2 → ProcessAccess
  | .assign t e => (e.rdW wd ++ t.rdW wd, t.mayW wd)
  | .alwaysComb b | .alwaysFF _ b | .alwaysPlain _ b | .alwaysFFR _ _ b _ =>
      (b.preemptReads wd, b.mayW wd)
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

/-- The first conflict that can expose a partial write.  `atomic` is true for
one-shot continuous assignments and NBA-only edge bodies; two such processes
may be interleaved without making an intermediate state visible. -/
def firstPreemptUnsafe
    (ps : List (Bool × ProcessAccess)) (i : Nat) : Option (Nat × Nat) :=
  match ps with
  | [] => none
  | (atomicA, a) :: rest =>
      match rest.findIdx? (fun (atomicB, b) =>
        (!atomicA || !atomicB) && a.conflicts b) with
      | some j => some (i, i + j + 1)
      | none => firstPreemptUnsafe rest (i + 1)

/-- The first refusal for the preemptive profile, if any. -/
def Design2.preemptionReport (m : Design2) : Option (String × String) :=
  let wd := m.combWd
  let accesses := m.processes.toList.map fun p => (p.preemptAtomic, p.preemptAccess wd)
  match firstPreemptUnsafe accesses 0 with
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

/-! ## The M0/E route

The M0 AST has no selects, so its access walk is deliberately smaller than
the semantic-tier one.  It is still bit-window based: a whole identifier is a
window at the instantiated declaration width, and a missing declaration is
left empty so the normal interpreter can report its own loud name error. -/

def Design.preemptWd (d : Design) (n : String) : Option Nat :=
  (d.decls.toList.map fun dc => (dc.name, dc.width)).lookup n

def preemptWhole (wd : String → Option Nat) (n : String) : List BWin :=
  match wd n with
  | some w => [(n, 0, w)]
  | none => []

mutual
  def Expr.preemptReads (wd : String → Option Nat) : Expr → List BWin
    | .lit _ | .unsupported _ _ => []
    | .ident n => preemptWhole wd n
    | .unary _ a | .reduce _ a | .resizeSigned _ a | .squash2 a =>
        a.preemptReads wd
    | .binary _ a b => a.preemptReads wd ++ b.preemptReads wd
    | .ternary c a b => c.preemptReads wd ++ a.preemptReads wd ++ b.preemptReads wd
    | .concat parts => Expr.listPreemptReads wd parts.toList
    termination_by structural e => e

  def Expr.listPreemptReads (wd : String → Option Nat) : List Expr → List BWin
    | [] => []
    | e :: rest => e.preemptReads wd ++ Expr.listPreemptReads wd rest
    termination_by structural es => es

  def Stmt.preemptReads (wd : String → Option Nat) : Stmt → List BWin
    | .blockingAssign t e | .nbaAssign t e =>
        e.preemptReads wd ++ preemptWhole wd t
    | .ifStmt c t e =>
        c.preemptReads wd ++ t.preemptReads wd ++ Stmt.optPreemptReads wd e
    | .block ss => Stmt.listPreemptReads wd ss.toList
    | .unsupported _ _ => []
    termination_by structural s => s

  def Stmt.optPreemptReads (wd : String → Option Nat) : Option Stmt → List BWin
    | none => []
    | some s => s.preemptReads wd
    termination_by structural o => o

  def Stmt.listPreemptReads (wd : String → Option Nat) : List Stmt → List BWin
    | [] => []
    | s :: rest => s.preemptReads wd ++ Stmt.listPreemptReads wd rest
    termination_by structural ss => ss
end

mutual
  def Stmt.preemptWrites (wd : String → Option Nat) : Stmt → List BWin
    | .blockingAssign t _ | .nbaAssign t _ => preemptWhole wd t
    | .ifStmt _ t e => t.preemptWrites wd ++ Stmt.optPreemptWrites wd e
    | .block ss => Stmt.listPreemptWrites wd ss.toList
    | .unsupported _ _ => []
    termination_by structural s => s

  def Stmt.optPreemptWrites (wd : String → Option Nat) : Option Stmt → List BWin
    | none => []
    | some s => s.preemptWrites wd
    termination_by structural o => o

  def Stmt.listPreemptWrites (wd : String → Option Nat) : List Stmt → List BWin
    | [] => []
    | s :: rest => s.preemptWrites wd ++ Stmt.listPreemptWrites wd rest
    termination_by structural ss => ss
end

def Process.preemptAccess (wd : String → Option Nat) : Process → ProcessAccess
  | .assign t e => (e.preemptReads wd, preemptWhole wd t)
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysComb b =>
      (b.preemptReads wd, b.preemptWrites wd)
  | .unsupported _ _ => ([], [])

mutual
  def Stmt.preemptNBAOnly : Stmt → Bool
    | .nbaAssign _ _ => true
    | .blockingAssign _ _ => false
    | .ifStmt _ t e => Stmt.preemptNBAOnly t && Stmt.optPreemptNBAOnly e
    | .block ss => Stmt.listPreemptNBAOnly ss.toList
    | .unsupported _ _ => false
    termination_by structural s => s

  def Stmt.optPreemptNBAOnly : Option Stmt → Bool
    | none => true
    | some s => Stmt.preemptNBAOnly s
    termination_by structural o => o

  def Stmt.listPreemptNBAOnly : List Stmt → Bool
    | [] => true
    | s :: rest => Stmt.preemptNBAOnly s && Stmt.listPreemptNBAOnly rest
    termination_by structural ss => ss
end

def Process.preemptAtomic : Process → Bool
  | .assign _ _ => true
  | .alwaysFF _ b | .alwaysPlain _ b => Stmt.preemptNBAOnly b
  | _ => false

def Design.preemptionReport (d : Design) : Option (String × String) :=
  let wd := d.preemptWd
  let accesses := d.processes.toList.map fun p =>
    (p.preemptAtomic, p.preemptAccess wd)
  match firstPreemptUnsafe accesses 0 with
  | none => none
  | some (i, j) =>
      some ("Schedule:preemptive",
        s!"processes {i} and {j} may observe an intermediate write under IEEE 1800-2023 §4.7; the default route requires disjoint partial-write windows")

def Design.preemptionAdmits (d : Design) : Bool := d.preemptionReport.isNone

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
      .alwaysFF "clk" (.nbaAssign (.ident "q") (.ident "a")),
      .alwaysFF "clk" (.blockingAssign (.ident "r") (.ident "q"))] }

private def safeNba : Design2 :=
  { indep with
    name := "preempt_safe_nba"
    processes := #[
      .alwaysFF "clk" (.nbaAssign (.ident "q") (.ident "a")),
      .alwaysFF "clk" (.nbaAssign (.ident "r") (.ident "q"))] }

#guard indep.preemptionReport == none
#guard safeNba.preemptionReport == none
#guard dep.preemptionAdmits == false
#guard match dep.preemptionReport with
  | some ("Schedule:preemptive", _) => true
  | _ => false
#guard dep.preemptionGuard.processes.toList.any fun p =>
  match p with | .unsupported "Schedule:preemptive" _ => true | _ => false

end LeanModels.Sv
