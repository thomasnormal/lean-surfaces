import LeanModels.Sv.CombEBase
import LeanModels.Core.Outcome

/-!
# E-core-0: the smallest slice of the authoritative semantics E (`LeanModels.Sv.Kernel`)

Experiment X1 of `svgolf/design/architecture/ARCH-NOTE.md` §7, designed in
`svgolf/design/architecture/X1-NOTE.md`. **Status: trusted** (these
definitions are the authority for the E-core-0 fragment); the theorems below
are *derived from E*, the `combSettle2` agreement is a *transport theorem*
(first slice), and `exec` is a test instrument with one soundness lemma.

## The fragment

One flat module, one time slot, the Active region only: continuous assigns
(`Proc0.assign`) and, since gate G-B, `always_comb` (`Proc0.comb`, run by `execBody`). 4-state, no timing, no NBA, no hierarchy, no loops.

## The shape (ARCH-NOTE §4.1)

* **Store.** `Store := VarId → Val`; `Val` carries its type (width,
  signedness, 2- or 4-state) and its bits, the width by construction. A write
  keeps the type and converts to it (`VType.conv`, LRM 6.11).
* **Names.** Expressions keep `Expr2`'s identifiers and are evaluated by
  `evalPure2 (E.view s) e`: `Elab.view` is the flat scope's declaration table
  read out of the store, so `evalPure2` IS E's expression evaluator (and is in
  E-core-0's trusted cone; debt D-X1b of the note).
* **Choice.** `Choice := ScheduleOracle`; its `choose_perm` is the legality
  predicate `Legal`. At each step the Choice orders the WHOLE current ready
  list and its head runs: any ready process may run next.
* **Process atomicity** (the declared profile ruling on LRM 4.7): one
  activation of a process is one micro-step (`activate`, written in the
  family monad `SemMWith`). After it, every process whose sensitivity
  (`Elab.sens`, the longest static prefixes it reads, `Expr2.reads`) saw a
  change becomes ready (`Elab.triggered`), unless already ready.
* **No fuel.** `step` is not recursive; behaviours are the inductive closure
  `Steps`; `SlotCloses` says the Active region drained. The only fuel is the
  test executor `exec`, with its one lemma `exec_sound`.
-/

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

/-! ## Names, types, values, stores -/

/-- A path segment of a structured name (instance, generate iteration,
named block). E-core-0 is flat: every path is `[]`. -/
inductive Seg where
  | inst (k : Nat)
  | gen (k : Nat) (i : Int)
  | blk (k : Nat)
deriving Repr, DecidableEq, Inhabited

/-- A variable: a scope path and the index of its declaration in that scope.
Never a string. -/
structure VarId where
  path : List Seg := []
  decl : Nat
deriving Repr, DecidableEq, Inhabited

/-- A value's type: width, signedness, 2-state or 4-state. -/
structure VType where
  width : Nat
  signed : Bool := false
  fourState : Bool := true
deriving Repr, DecidableEq, Inhabited

/-- The declared type of a declaration. -/
def VType.ofDecl (dc : Decl) : VType :=
  { width := dc.width, signed := dc.isSigned, fourState := !dc.twoState }

/-- Conversion into a type's value set: a 2-state type maps x/z to 0 (LRM 6.11);
a 4-state type keeps every bit. -/
def VType.conv (ty : VType) (v : LVec) : LVec :=
  if ty.fourState then v else v.toTwoState

theorem VType.width_conv (ty : VType) (v : LVec) : (ty.conv v).width = v.width := by
  unfold VType.conv
  split
  · rfl
  · simp [LVec.toTwoState, LVec.width]

theorem VType.conv_of_four {ty : VType} (h : ty.fourState = true) (v : LVec) :
    ty.conv v = v := by
  simp [VType.conv, h]

/-- A typed value: its bits always have the type's width. -/
structure Val where
  ty : VType
  bits : LVec
  width_eq : bits.width = ty.width

/-- A value of type `ty` from any vector: resized to the width, converted to the
type's value set. -/
def Val.ofLVec (ty : VType) (v : LVec) : Val :=
  ⟨ty, ty.conv (v.resizeU ty.width), by rw [VType.width_conv, LVec.width_resizeU]⟩

/-- Select-write `part` at bit `lo` (bits beyond the width are dropped); the type
is kept and the result converted to it. -/
def Val.write (x : Val) (lo : Nat) (part : LVec) : Val :=
  ⟨x.ty, x.ty.conv (x.bits.insertAt lo part),
    by rw [VType.width_conv, LVec.width_insertAt, x.width_eq]⟩

instance : Inhabited Val := ⟨Val.ofLVec { width := 0 } ⟨#[]⟩⟩

/-- The store: every variable's current value. -/
abbrev Store := VarId → Val

/-- Overwrite one variable. -/
def Store.set (s : Store) (x : VarId) (v : Val) : Store :=
  fun y => if y = x then v else s y

/-! ## The elaborated design -/

/-- A process of E-core-0. The syntax is the frozen `Lhs2`/`Expr2`/`Stmt2`
(no constructor is added). -/
inductive Proc0 where
  | assign (target : Lhs2) (rhs : Expr2)
  | comb (body : Stmt2)
  /-- Plain `always @*` (§9.4.2.2): the process starts waiting and is
  reactivated only by a change in its raw read set.  Its body is the same
  source-shaped `Stmt2` engine as `always_comb`; only startup/sensitivity
  metadata differs. -/
  | implicit (body : Stmt2)
deriving Inhabited

/-- A process index. -/
abbrev ProcId := Nat

/-- The elaborated E-core-0 design: one flat scope (declaration `i` is the
variable `⟨[], i⟩`) and its processes. -/
structure Elab where
  decls : Array Decl
  procs : Array Proc0
  /-- The module's name (carried to the corresponding Design2; E never reads it). -/
  name : String := "core0"

def Proc0.toProcess2 : Proc0 → Process2
  | .assign t e => .assign t e
  | .comb body => .alwaysComb body
  | .implicit _ => .unsupported "ProceduralBlockSymbol:Always"
      "source-level event-controlled always is retained; the frozen process AST has no event-list constructor"

/-- The corresponding Design2: the same declarations, each process its
syntactic image. Only the statements about `combSettle2` and the reused
profile (`CombDesign`, debt D-X1a) mention it; E does not. -/
def Elab.toDesign2 (E : Elab) : Design2 :=
  { name := E.name, decls := E.decls,
    processes := (E.procs.toList.map Proc0.toProcess2).toArray }

/-! ## Design2 transport (the E-side elaboration entry point) -/

def Proc0.ofProcess2 : Process2 → Proc0
  | .assign t e => .assign t e
  | .alwaysComb b => .comb b
  | .unsupported k x => .comb (.unsupported k x)
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ _ =>
      .comb (.unsupported "always_ff" "clocked processes are outside E-core-0")

def Elab.ofDesign2 (d : Design2) : Elab :=
  { decls := d.decls
    procs := (d.processes.toList.map Proc0.ofProcess2).toArray
    name := d.name }

/-- The declaration a variable names (flat scope only). -/
def Elab.declOf (E : Elab) (x : VarId) : Option Decl :=
  match x.path with
  | [] => E.decls[x.decl]?
  | _ :: _ => none

/-- First declaration named `n` at or after position `i`. -/
def resolveAux (n : String) : List Decl → Nat → Option VarId
  | [], _ => none
  | dc :: ds, i => if dc.name == n then some { decl := i } else resolveAux n ds (i + 1)

/-- Name resolution in the flat scope (the first declaration of the name, as
`SvState.lookup` finds it). -/
def Elab.resolve (E : Elab) (n : String) : Option VarId :=
  resolveAux n E.decls.toList 0

/-- The declarations from position `i` on, read out of the store. -/
def viewAux (s : Store) : List Decl → Nat → SvState
  | [], _ => []
  | dc :: ds, i => (dc.name, (s { decl := i }).bits) :: viewAux s ds (i + 1)

/-- **The view**: the store read through the declaration table, as the
name-keyed state `evalPure2` reads. This is E-core-0's name resolution
(debt D-X1b), and the only bridge between `Store` and `SvState`. -/
def Elab.view (E : Elab) (s : Store) : SvState :=
  viewAux s E.decls.toList 0

/-- The store is typed: every declared variable holds a value of its declared
type. -/
def Elab.Typed (E : Elab) (s : Store) : Prop :=
  ∀ x dc, E.declOf x = some dc → (s x).ty = VType.ofDecl dc

/-- The startup store: declaration initializers, else all-x (LRM 6.8). -/
def Elab.initStore (E : Elab) : Store := fun x =>
  match E.declOf x with
  | some dc =>
      Val.ofLVec (VType.ofDecl dc)
        (dc.init.getD (if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width))
  | none => default

/-- Set a named variable from a vector (stimulus; converted to its type). -/
def Elab.setName (E : Elab) (s : Store) (n : String) (v : LVec) : Store :=
  match E.resolve n with
  | some x => s.set x (Val.ofLVec (s x).ty v)
  | none => s

/-- Write `part` into window `[lo, …)` of the variable named `n`. -/
def Elab.writeWin (E : Elab) (s : Store) (n : String) (lo : Nat) (part : LVec) : Store :=
  match E.resolve n with
  | some x => s.set x ((s x).write lo part)
  | none => s

/-- Write the placed windows of a value, in list order (`((n, lo, w), off)`
receives `val.extract off w`): the store image of `SvState.writeWins`. -/
def Elab.writeWins (E : Elab) (s : Store) (val : LVec) : List (Win × Nat) → Store
  | [] => s
  | ((n, lo, w), off) :: rest => E.writeWins (E.writeWin s n lo (val.extract off w)) val rest

/-! ## One activation, in the family monad -/

/-- E-core-0's activation monad: Core's `SemMWith` with the store as world,
no language raise (`Empty`: a comb activation cannot raise), and `String`
refusal payloads `"<clause>: <message>"` (debt D-X1c). -/
abbrev EM := SemMWith Store Empty String Unit

/-- A loud refusal citing an IEEE 1800 clause. -/
def refuse0 {α : Type} (clause msg : String) : EM α :=
  LeanModels.refuse (.unsupported clause) s!"{clause}: {msg}"

/-- Lift a fuel-free evaluation (`evalPure2` never times out). -/
def ofRes {α : Type} : Res α → EM α
  | .ok a => pure a
  | .timeout => LeanModels.exhausted
  | .unsupported m => refuse0 "11" m

/-! ## `always_comb` bodies

A body runs WHOLE as one activation (process atomicity: no comb body has a
suspension point). Its statements are executed by `execBody`, a fuel-free
structural recursion over the frozen `Stmt2` syntax: blocking assignments to
STATIC targets (a whole signal, a constant slice, a constant-literal element
select, inside the declared width: LRM 11.5.1), `if`, `case`/`case inside`
(first matching arm; a `unique`/`unique0`/`priority` claim that does not hold refuses at once,
`CaseCheck:<qualifier>`, a known divergence from LRM 12.4.2.1, which defers the report and flushes it
on re-trigger: X1-NOTE §13; `casez`/`casex` refuse, outside the profile) and
`begin … end`. Nonblocking assignments, dynamic or concatenated targets and
`.unsupported` nodes are refused loudly (outside E-core-0). -/

end LeanModels.Sv.Kernel

/-! The static data of a body (syntax-level, so in the `Sv` namespace for
field notation). -/

namespace LeanModels.Sv

/-- The static write window of a blocking-assignment target. -/
def Lhs2.staticWin (d : Design2) (t : Lhs2) : Option Win :=
  match t with
  | .concat _ => none
  | _ =>
      (t.window? d).bind fun W =>
        (d.declWidth W.1).bind fun dw => if W.2.1 + W.2.2 ≤ dw then some W else none

mutual

/-- Every longest static prefix a body reads (right-hand sides, conditions,
case subjects and patterns), in source order. -/
def Stmt2.rawReads : Stmt2 → List ReadWin
  | .blockingAssign _ e => e.reads
  | .nbaAssign _ e => e.reads
  | .ifStmt c t e => c.reads ++ t.rawReads ++ Stmt2.optRawReads e
  | .block body => Stmt2.listRawReads body.toList
  | .caseStmt subj items dflt _ _ =>
      subj.reads ++ CaseItem2.listRawReads items.toList ++ Stmt2.optRawReads dflt
  | .unsupported _ _ => []
termination_by structural s => s

def Stmt2.optRawReads : Option Stmt2 → List ReadWin
  | none => []
  | some s => s.rawReads
termination_by structural o => o

def Stmt2.listRawReads : List Stmt2 → List ReadWin
  | [] => []
  | s :: ss => s.rawReads ++ Stmt2.listRawReads ss
termination_by structural ss => ss

def CaseItem2.rawReads : CaseItem2 → List ReadWin
  | .mk pats body => Expr2.listReads pats.toList ++ body.rawReads
termination_by structural it => it

def CaseItem2.listRawReads : List CaseItem2 → List ReadWin
  | [] => []
  | it :: rest => it.rawReads ++ CaseItem2.listRawReads rest
termination_by structural its => its

end

mutual

/-- Every static window a body may write (its blocking targets). -/
def Stmt2.targetWins (d : Design2) : Stmt2 → List Win
  | .blockingAssign t _ => (Lhs2.staticWin d t).toList
  | .nbaAssign _ _ => []
  | .ifStmt _ t e => t.targetWins d ++ Stmt2.optTargetWins d e
  | .block body => Stmt2.listTargetWins d body.toList
  | .caseStmt _ items dflt _ _ =>
      CaseItem2.listTargetWins d items.toList ++ Stmt2.optTargetWins d dflt
  | .unsupported _ _ => []
termination_by structural s => s

def Stmt2.optTargetWins (d : Design2) : Option Stmt2 → List Win
  | none => []
  | some s => s.targetWins d
termination_by structural o => o

def Stmt2.listTargetWins (d : Design2) : List Stmt2 → List Win
  | [] => []
  | s :: ss => s.targetWins d ++ Stmt2.listTargetWins d ss
termination_by structural ss => ss

def CaseItem2.targetWins (d : Design2) : CaseItem2 → List Win
  | .mk _ body => body.targetWins d
termination_by structural it => it

def CaseItem2.listTargetWins (d : Design2) : List CaseItem2 → List Win
  | [] => []
  | it :: rest => it.targetWins d ++ CaseItem2.listTargetWins d rest
termination_by structural its => its

end

/-- The bits of a read that the windows `ws` do not cover, as 1-bit windows (a whole read of an
undeclared name has none). -/
def ReadWin.unwrittenBits (d : Design2) (ws : List Win) : ReadWin → List ReadWin
  | .whole n => ((List.range ((d.declWidth n).getD 0)).filter fun i =>
      !(ws.any fun W => (ReadWin.win n i 1).overlaps W)).map fun i => ReadWin.win n i 1
  | .win n lo w => ((List.range w).filter fun k =>
      !(ws.any fun W => (ReadWin.win n (lo + k) 1).overlaps W)).map fun k => ReadWin.win n (lo + k) 1

/-- **The bits of a partly written read that the block still senses** (LRM 9.2.2.2.1: the
implicit sensitivity leaves out only what the block itself writes). For every read that overlaps a
window the body writes, its bits outside every written window, as 1-bit windows. A read that the
body writes entirely contributes nothing; a read it does not write at all is not here (it is in
the sensitivity whole). -/
def Stmt2.partialSens (d : Design2) (body : Stmt2) : List ReadWin :=
  (body.rawReads.filter fun r => (body.targetWins d).any fun W => r.overlaps W).flatMap
    (ReadWin.unwrittenBits d (body.targetWins d))

end LeanModels.Sv

namespace LeanModels.Sv.Kernel

/-- How many arms of a `case` match (every arm's patterns evaluated: LRM 12.5.3's claims are about
the whole match set). -/
def caseHits (st : SvState) (sv : LVec) (mode : CaseMode) : List CaseItem2 → Res Nat
  | [] => .ok 0
  | .mk pats _ :: rest => do
      let pvs ← evalPures2 st pats.toList
      let n ← caseHits st sv mode rest
      return (if pvs.any (fun pv => caseHit mode sv pv) then n + 1 else n)

/-- The `case` modes in E-core-0's profile: plain `case` and `case … inside`. `casez`/`casex`
(LRM 12.5.1) refuse loudly (`caseModeRefusal`); they never fall through to plain-case meaning. -/
def caseModeInE0 : CaseMode → Bool
  | .normal | .inside => true
  | .casez | .casex => false

/-- The refusal text for a mode outside the profile (CombProc's form: the statement, then why). -/
def caseModeRefusal : CaseMode → String
  | .normal => "always_comb statement `case` (outside E-core-0)"
  | .inside => "always_comb statement `case … inside` (outside E-core-0)"
  | .casez => "always_comb statement `casez` (outside E-core-0)"
  | .casex => "always_comb statement `casex` (outside E-core-0)"

/-- LRM 12.5.3's claims, as `run2` checks them (`checkCaseObligation`, master 2218821b): `unique`,
exactly one arm matches or none and a default exists; `unique0`, at most one; `priority`, at least
one or a default. -/
def caseClaimOk : CaseCheck → Bool → Nat → Bool
  | .none, _, _ => true
  | .unique, hasDefault, n => n == 1 || (n == 0 && hasDefault)
  | .unique0, _, n => decide (n ≤ 1)
  | .priority, hasDefault, n => decide (1 ≤ n) || hasDefault

/-- `run2`'s names for a violated claim. -/
def caseCheckName : CaseCheck → String
  | .none => "CaseCheck:none"
  | .unique => "CaseCheck:unique"
  | .unique0 => "CaseCheck:unique0"
  | .priority => "CaseCheck:priority"

mutual

/-- **Execute an `always_comb` body** (fuel-free, structural). A qualified `case` (`unique`,
`unique0`, `priority`) whose claim does not hold refuses loudly with `run2`'s name
(`CaseCheck:<qualifier>`); when it holds, the first matching arm runs, as for a plain `case`. -/
def execBody (E : Elab) : Stmt2 → EM Unit
  | .blockingAssign t e =>
      match Lhs2.staticWin E.toDesign2 t with
      | some (n, lo, w) => do
          let s ← get
          let v ← ofRes (evalPure2 (E.view s) e)
          set (E.writeWin s n lo (v.resizeU w))
      | none => refuse0 "10.4.1" "blocking assignment target is not a static in-range window"
  | .nbaAssign _ _ => refuse0 "9.2.2.2" "nonblocking assignment in always_comb is outside E-core-0"
  | .ifStmt c t e => do
      let s ← get
      let cv ← ofRes (evalPure2 (E.view s) c)
      if cv.condTrue then execBody E t else execBodyOpt E e
  | .block body => execBodyList E body.toList
  | .caseStmt subj items dflt mode check =>
      if caseModeInE0 mode then do
        let s ← get
        let sv ← ofRes (evalPure2 (E.view s) subj)
        match check with
        | .none =>
            let hit ← execArms E sv mode items.toList
            if hit then pure () else execBodyOpt E dflt
        | chk =>
            let n ← ofRes (caseHits (E.view s) sv mode items.toList)
            if caseClaimOk chk dflt.isSome n then
              let hit ← execArms E sv mode items.toList
              if hit then pure () else execBodyOpt E dflt
            else refuse0 "12.5.3" (caseCheckName chk)
      else refuse0 "12.5.1" (caseModeRefusal mode)
  | .unsupported k _ => refuse0 "12" s!"unsupported statement '{k}'"
termination_by structural s => s

def execBodyOpt (E : Elab) : Option Stmt2 → EM Unit
  | none => pure ()
  | some s => execBody E s
termination_by structural o => o

def execBodyList (E : Elab) : List Stmt2 → EM Unit
  | [] => pure ()
  | s :: ss => do
      execBody E s
      execBodyList E ss
termination_by structural ss => ss

/-- One `case` arm: evaluate its patterns; on a hit run its body and report
`true` (first match wins, LRM 12.5). -/
def execArm (E : Elab) (sv : LVec) (mode : CaseMode) : CaseItem2 → EM Bool
  | .mk pats body => do
      let s ← get
      let pvs ← ofRes (evalPures2 (E.view s) pats.toList)
      if pvs.any (fun pv => caseHit mode sv pv) then do
        execBody E body
        pure true
      else pure false
termination_by structural it => it

def execArms (E : Elab) (sv : LVec) (mode : CaseMode) : List CaseItem2 → EM Bool
  | [] => pure false
  | it :: rest => do
      let hit ← execArm E sv mode it
      if hit then pure true else execArms E sv mode rest
termination_by structural its => its

end

/-- **One process-atomic activation.** A continuous assign evaluates its
right-hand side on the current store and writes the result, resized to the
target's total width, into the target's static windows (MSB-first,
`Win.placed`). An `always_comb` runs its whole body (`execBody`). -/
def activate (E : Elab) (p : ProcId) : EM Unit :=
  match E.procs[p]? with
  | some (.assign t e) =>
      match t.windows? E.toDesign2 with
      | some ws => do
          let s ← get
          let v ← ofRes (evalPure2 (E.view s) e)
          set (E.writeWins s (v.resizeU (Win.sumWidth ws)) (Win.placed ws))
      | none => refuse0 "10.3.2" "continuous assignment target has no static window"
  | some (.comb body) | some (.implicit body) => execBody E body
  | none => refuse0 "4.5" "no such process"

/-! ## Sensitivity and triggering -/

instance (st st' : SvState) (r : ReadWin) : Decidable (r.agree st st') := by
  cases r <;> unfold ReadWin.agree <;> infer_instance

/-- A process's sensitivity: the longest static prefixes it reads. A continuous assign is
sensitive to its right-hand side's reads. An `always_comb` is sensitive to its body's reads EXCEPT
the bits the body writes (LRM 9.2.2.2.1: the expansions of the reads, less what the block writes;
the block is never woken by its own writes): a read the body does not write is in whole, and of a
read that overlaps a written window, its unwritten bits (`Stmt2.partialSens`). Before 2026-11-03 a
partly written read was dropped whole, Icarus's reading; agent M's X2 measured the pinned Xcelium
row `acg_xproc_bits` against that, and `Core0Smoke.xprocBits` now pins the row. -/
def Elab.sens (E : Elab) (q : ProcId) : List ReadWin :=
  match E.procs[q]? with
  | some (.assign _ e) => e.reads
  | some (.comb body) =>
      body.rawReads.filter (fun r => !((body.targetWins E.toDesign2).any fun W => r.overlaps W)) ++
        body.partialSens E.toDesign2
  | some (.implicit body) => body.rawReads
  | none => []

/-- A read of the body that overlaps no written window is in the sensitivity (the statement agent
L's `sens_of_read` needs). -/
theorem Elab.mem_sens_of_raw {E : Elab} {q : ProcId} {body : Stmt2}
    (hp : E.procs[q]? = some (.comb body)) {r : ReadWin} (hr : r ∈ body.rawReads)
    (hno : ∀ W ∈ body.targetWins E.toDesign2, r.overlaps W = false) : r ∈ E.sens q := by
  simp only [Elab.sens, hp]
  refine List.mem_append_left _ (List.mem_filter.mpr ⟨hr, ?_⟩)
  simp only [Bool.not_eq_true', List.any_eq_false]
  exact fun W hW hov => by rw [hno W hW] at hov; cases hov

/-! Plain `always @*` has the source rule's raw-read sensitivity. Unlike
`always_comb`, its read set is not reduced by writes in the same body. -/

theorem Elab.sens_implicit_eq {E : Elab} {q : ProcId} {body : Stmt2}
    (hp : E.procs[q]? = some (.implicit body)) : E.sens q = body.rawReads := by
  simp only [Elab.sens, hp]

theorem Elab.mem_sens_of_raw_implicit {E : Elab} {q : ProcId} {body : Stmt2}
    (hp : E.procs[q]? = some (.implicit body)) {r : ReadWin}
    (hr : r ∈ body.rawReads) : r ∈ E.sens q := by
  rw [Elab.sens_implicit_eq hp]
  exact hr

/-- `q` is triggered by the change from `st` to `st'`: an element of its
sensitivity changed. -/
def Elab.Triggered (E : Elab) (st st' : SvState) (q : ProcId) : Prop :=
  ∃ r ∈ E.sens q, ¬ r.agree st st'

/-- Every triggered process, in index order. -/
def Elab.triggered (E : Elab) (st st' : SvState) : List ProcId :=
  (List.range E.procs.size).filter fun q => (E.sens q).any fun r => !decide (r.agree st st')

/-! ## Configurations, legality, the step -/

/-- A configuration inside one time slot: the store, the Active region's ready
set (duplicate-free under `SettleInv`), and the Choice invocation counter. -/
structure Config where
  store : Store
  active : List ProcId
  k : Nat := 0

/-- A process's scheduling state, derived from the configuration. E-core-0
has no suspension points inside an activation, so there are no frames and no
`done` (comb processes never finish). -/
inductive Status where
  | ready
  | waiting (sens : List ReadWin)

structure ProcState where
  status : Status

def Config.procState (E : Elab) (c : Config) (q : ProcId) : ProcState :=
  if q ∈ c.active then ⟨.ready⟩ else ⟨.waiting (E.sens q)⟩

/-- **The legal-schedule predicate**: every invocation orders the whole ready
list (a permutation: nothing dropped, nothing invented). -/
def Legal (choose : Nat → List ProcId → List ProcId) : Prop :=
  ∀ k ready, (choose k ready).Perm ready

/-- A Choice is a legal schedule: `ScheduleOracle` bundles the choice function
with its `Legal` proof (`choose_perm`). -/
abbrev Choice := ScheduleOracle

theorem Choice.legal (ch : Choice) : Legal ch.choose := ch.choose_perm

/-- The start of a slot in which every process is ready (time zero, or after
an arbitrary change). -/
def Proc0.readyAtStart : Proc0 → Bool
  | .implicit _ => false
  | .assign _ _ | .comb _ => true

def Elab.startActive (E : Elab) : List ProcId :=
  (List.range E.procs.size).filter fun q =>
    match E.procs[q]? with
    | some p => p.readyAtStart
    | none => false

def Config.init (E : Elab) (s : Store) : Config :=
  { store := s, active := E.startActive, k := 0 }

/-! ## Slots and the environment's input events (E-core-0: no clocks) -/

/-- **The input events at the start of a slot.** Every declared input port the
entry binds takes the bound value, converted to the port's type (width and
2- or 4-state: LRM 6.11, 10.7); every other variable holds its value. -/
def Elab.applyInputs (E : Elab) (s : Store) (entry : SvState) : Store := fun x =>
  match E.declOf x with
  | some dc =>
      if dc.isInput then
        match SvState.lookup entry dc.name with
        | some v => Val.ofLVec (s x).ty v
        | none => s x
      else s x
  | none => s x

/-- **A new slot** after a closed one: the input events update the store, and
every process sensitive to an element that changed becomes ready (LRM 4.3: an
update event wakes the processes waiting on it). The Choice counter carries on. -/
def Config.nextSlot (E : Elab) (c : Config) (entry : SvState) : Config :=
  { store := E.applyInputs c.store entry
    active := E.triggered (E.view c.store) (E.view (E.applyInputs c.store entry))
    k := c.k }

/-- **Time zero**: the startup store with the first input events applied, every
process ready (continuous assignments and `always_comb` are evaluated at time
zero). -/
def Config.start (E : Elab) (entry : SvState) : Config :=
  Config.init E (E.applyInputs E.initStore entry)

inductive StepResult where
  | next (c : Config)
  | slotClosed (c : Config)
  | refused (r : Loud String Unit)

/-- **One micro-step** (total, not recursive). The Choice orders the ready list;
its head runs as one atomic activation; the processes it triggered join the
ready set. An empty ready list closes the slot. -/
def step (E : Elab) (ch : Choice) (c : Config) : StepResult :=
  match ch.choose c.k c.active with
  | [] => .slotClosed c
  | p :: rest =>
      match activate E p c.store with
      | .ok (_, s') =>
          .next { store := s'
                  active := rest ++ (E.triggered (E.view c.store) (E.view s')).filter
                    (fun q => decide (q ∉ rest))
                  k := c.k + 1 }
      | .error l => .refused l

/-- **Behaviours inside a slot**: the reflexive-transitive closure of `step`. -/
inductive Steps (E : Elab) (ch : Choice) : Config → Config → Prop where
  | refl (c : Config) : Steps E ch c c
  | head {c c' c'' : Config} : step E ch c = .next c' → Steps E ch c' c'' → Steps E ch c c''

/-- The slot closes at `c'`: reached, and the Active region is drained. -/
def SlotCloses (E : Elab) (ch : Choice) (c c' : Config) : Prop :=
  Steps E ch c c' ∧ step E ch c' = .slotClosed c'

/-! ## The test executor (the only fuel) -/

inductive ExecResult where
  | closed (c : Config)
  | refused (r : Loud String Unit)
  | outOfBudget (c : Config)

/-- Iterate `step` under one Choice, at most `n` times. A harness instrument,
not a semantics: `exec_sound`. -/
def exec (E : Elab) (ch : Choice) : Nat → Config → ExecResult
  | 0, c => .outOfBudget c
  | n + 1, c =>
      match step E ch c with
      | .next c' => exec E ch n c'
      | .slotClosed c' => .closed c'
      | .refused r => .refused r

theorem step_slotClosed {E : Elab} {ch : Choice} {c c' : Config}
    (h : step E ch c = .slotClosed c') : c' = c := by
  unfold step at h
  split at h
  · cases h; rfl
  · split at h <;> cases h

/-- **The executor is sound**: a closed result is a closed slot. -/
theorem exec_sound {E : Elab} {ch : Choice} :
    ∀ {n : Nat} {c c' : Config}, exec E ch n c = .closed c' → SlotCloses E ch c c'
  | 0, _, _, h => by simp [exec] at h
  | n + 1, c, c', h => by
      simp only [exec] at h
      cases hs : step E ch c with
      | next c₁ =>
          simp only [hs] at h
          obtain ⟨hst, hcl⟩ := exec_sound h
          exact ⟨.head hs hst, hcl⟩
      | slotClosed c₁ =>
          simp only [hs, ExecResult.closed.injEq] at h
          subst h
          obtain rfl := step_slotClosed hs
          exact ⟨.refl _, hs⟩
      | refused r => simp [hs] at h

/-! ## Legality: the no-skip lemma -/

/-- **No ready process is skipped, and none runs unless ready.** In a step from a
duplicate-free ready set: the process `p` that ran was ready; every other ready
process is still ready; every process ready afterwards was ready before (and is
not `p`) or was triggered by this step's change; and the ready set stays
duplicate-free. So a process leaves the Active region only by running, and runs
again only after a new trigger. -/
theorem step_legal {E : Elab} {ch : Choice} {c c' : Config} (hnd : c.active.Nodup)
    (h : step E ch c = .next c') :
    ∃ p, p ∈ c.active ∧
      (∀ q ∈ c.active, q ≠ p → q ∈ c'.active) ∧
      (∀ q ∈ c'.active, (q ∈ c.active ∧ q ≠ p) ∨
        q ∈ E.triggered (E.view c.store) (E.view c'.store)) ∧
      c'.active.Nodup := by
  have hperm := ch.choose_perm c.k c.active
  unfold step at h
  revert hperm
  cases hch : ch.choose c.k c.active with
  | nil => simp [hch] at h
  | cons p rest =>
      intro hperm
      simp only [hch] at h
      cases ha : activate E p c.store with
      | error l => simp [ha] at h
      | ok r =>
          obtain ⟨_, s'⟩ := r
          simp only [ha, StepResult.next.injEq] at h
          subst h
          have hnd' : (p :: rest).Nodup := hperm.nodup_iff.mpr hnd
          obtain ⟨hpr, hrest⟩ := List.nodup_cons.mp hnd'
          refine ⟨p, hperm.mem_iff.mp (List.mem_cons_self ..), ?_, ?_, ?_⟩
          · intro q hq hqp
            have : q ∈ p :: rest := hperm.mem_iff.mpr hq
            rcases List.mem_cons.mp this with rfl | hq'
            · exact absurd rfl hqp
            · exact List.mem_append_left _ hq'
          · intro q hq
            rcases List.mem_append.mp hq with hq | hq
            · left
              exact ⟨hperm.mem_iff.mp (List.mem_cons_of_mem _ hq),
                fun hqp => hpr (hqp ▸ hq)⟩
            · right
              exact (List.mem_filter.mp hq).1
          · refine List.nodup_append.mpr ⟨hrest, ?_, ?_⟩
            · exact (List.nodup_range.filter _).filter _
            · intro a ha b hb hab
              subst hab
              have := (List.mem_filter.mp hb).2
              simp only [decide_eq_true_eq] at this
              exact this ha

/-! ## Smoke tests: a three-assign chain, and the two negative designs -/

namespace Core0Smoke

/-- `b = a + 1; c = b + 1; d = c + 1`, listed in REVERSE dependency order. -/
def chain3 : Elab where
  decls := #[{ name := "a", width := 4, isInput := true }, { name := "b", width := 4 },
             { name := "c", width := 4 }, { name := "d", width := 4 }]
  procs := #[.assign (.ident "d") (.binary .add (.ident "c") (.lit (.ofNat 4 1))),
             .assign (.ident "c") (.binary .add (.ident "b") (.lit (.ofNat 4 1))),
             .assign (.ident "b") (.binary .add (.ident "a") (.lit (.ofNat 4 1)))]

def chain3Start : Config := Config.init chain3 (chain3.setName chain3.initStore "a" (.ofNat 4 5))

def showClosed (E : Elab) (names : List String) : ExecResult → Option (List String)
  | .closed c => some (names.map (SvState.showSignal (E.view c.store)))
  | _ => none

def isBudget : ExecResult → Bool
  | .outOfBudget _ => true
  | _ => false

/-! Source order runs `d` and `c` first on stale inputs (no change, no
trigger), then `b`, which re-triggers `c`, which re-triggers `d`: 5
activations. Reverse order runs `b` first: 4 activations. Same closed store
(`b = 6, c = 7, d = 8`); the budget rows pin the activation counts (one budget
unit per activation plus one for the closing step). -/
#guard showClosed chain3 ["a", "b", "c", "d"] (exec chain3 σ_src 6 chain3Start)
  == some ["0101", "0110", "0111", "1000"]
#guard isBudget (exec chain3 σ_src 5 chain3Start)
#guard showClosed chain3 ["a", "b", "c", "d"] (exec chain3 σ_rev 5 chain3Start)
  == some ["0101", "0110", "0111", "1000"]
#guard isBudget (exec chain3 σ_rev 4 chain3Start)

/-- `assign y = ~y` from `y = 0`: a zero-delay oscillation (cyclic). -/
def osc : Elab where
  decls := #[{ name := "y", width := 1, init := some (.ofNat 1 0) }]
  procs := #[.assign (.ident "y") (.unary .bnot (.ident "y"))]

/-! The oscillation never closes the slot: every activation flips `y` and
re-triggers itself. -/
#guard isBudget (exec osc σ_src 1000 (Config.init osc osc.initStore))
#guard isBudget (exec osc σ_rev 1000 (Config.init osc osc.initStore))

/-- `assign a = b; assign b = a` from `a = 0, b = 1` (cyclic). -/
def swap : Elab where
  decls := #[{ name := "a", width := 1, init := some (.ofNat 1 0) },
             { name := "b", width := 1, init := some (.ofNat 1 1) }]
  procs := #[.assign (.ident "a") (.ident "b"), .assign (.ident "b") (.ident "a")]

/-! Both schedules close the slot, at DIFFERENT stores: without a rank the
closed store is not unique. -/
#guard showClosed swap ["a", "b"] (exec swap σ_src 10 (Config.init swap swap.initStore))
  == some ["1", "1"]
#guard showClosed swap ["a", "b"] (exec swap σ_rev 10 (Config.init swap swap.initStore))
  == some ["0", "0"]

/-- Two assigns around one `always_comb` with a temporary and an `if`:
`always_comb begin t = a & b; if (c) y = t; else y = ~t; end`, `z = y + 1`,
`w = z ^ a` (listed against dependency order). -/
def mux1 : Elab where
  decls := #[{ name := "a", width := 4, isInput := true }, { name := "b", width := 4, isInput := true },
             { name := "c", width := 1, isInput := true }, { name := "t", width := 4 },
             { name := "y", width := 4 }, { name := "z", width := 4 }, { name := "w", width := 4 }]
  procs := #[.assign (.ident "w") (.binary .xor (.ident "z") (.ident "a")),
             .assign (.ident "z") (.binary .add (.ident "y") (.lit (.ofNat 4 1))),
             .comb (.block #[
               .blockingAssign (.ident "t") (.binary .and (.ident "a") (.ident "b")),
               .ifStmt (.ident "c") (.blockingAssign (.ident "y") (.ident "t"))
                 (some (.blockingAssign (.ident "y") (.unary .bnot (.ident "t"))))])]

def mux1Start (a b c : Nat) : Config :=
  Config.init mux1 (mux1.setName (mux1.setName (mux1.setName mux1.initStore "a" (.ofNat 4 a))
    "b" (.ofNat 4 b)) "c" (.ofNat 1 c))

/-! `a = 3, b = 5`: `t = 1`; `c = 1`: `y = 1, z = 2, w = 1`; `c = 0`: `y = 14,
z = 15, w = 12`. Both schedules close at the same store. -/
#guard showClosed mux1 ["t", "y", "z", "w"] (exec mux1 σ_src 20 (mux1Start 3 5 1))
  == some ["0001", "0001", "0010", "0001"]
#guard showClosed mux1 ["t", "y", "z", "w"] (exec mux1 σ_rev 20 (mux1Start 3 5 1))
  == some ["0001", "0001", "0010", "0001"]
#guard showClosed mux1 ["t", "y", "z", "w"] (exec mux1 σ_src 20 (mux1Start 3 5 0))
  == some ["0001", "1110", "1111", "1100"]
#guard showClosed mux1 ["t", "y", "z", "w"] (exec mux1 σ_rev 20 (mux1Start 3 5 0))
  == some ["0001", "1110", "1111", "1100"]

/-- A self-reading body, `always_comb begin y = t; t = a; end`: it reads `t`
before writing it. The block is never woken by its own write of `t`, so the
slot closes with `y` STALE (`x`, while `t = a = 0`). -/
def selfRead : Elab where
  decls := #[{ name := "a", width := 1, isInput := true }, { name := "t", width := 1 },
             { name := "y", width := 1 }]
  procs := #[.comb (.block #[.blockingAssign (.ident "y") (.ident "t"),
                             .blockingAssign (.ident "t") (.ident "a")])]

def selfReadStart : Config :=
  Config.init selfRead (selfRead.setName selfRead.initStore "a" (.ofNat 1 0))

#guard showClosed selfRead ["a", "t", "y"] (exec selfRead σ_src 10 selfReadStart)
  == some ["0", "0", "x"]

/-- **The pinned Xcelium row `acg_xproc_bits`** (`Examples/system-verilog/sem2/acg_xproc_bits`):
`always_comb t[0] = a;` beside `always_comb begin t[1] = b; y = t; end`. The second block senses
`t[0]` (LRM 9.2.2.2.1, Xcelium 24.03, Verilator, `run2`), so `y = {b, a}` in every cycle; Icarus
leaves all of `t` out (a declared Icarus departure). -/
def xprocBits : Elab where
  decls := #[{ name := "a", width := 1, isInput := true }, { name := "b", width := 1, isInput := true },
             { name := "y", width := 2, isOutput := true }, { name := "t", width := 2 }]
  procs := #[.comb (.blockingAssign (.slice "t" 0 1) (.ident "a")),
             .comb (.block #[.blockingAssign (.slice "t" 1 1) (.ident "b"),
                             .blockingAssign (.ident "y") (.ident "t")])]

/-- Run slots with the given input events from a closed configuration; `y` after each. -/
def runYs (E : Elab) (ch : Choice) : Config → List SvState → Option (List String)
  | _, [] => some []
  | c, e :: es =>
      match exec E ch 50 (Config.nextSlot E c e) with
      | .closed c' => (runYs E ch c' es).map (SvState.showSignal (E.view c'.store) "y" :: ·)
      | _ => none

/-- The row's stimulus (`harness/sv/cases2.json`). -/
def xprocStim : List SvState :=
  [[("a", .ofNat 1 0), ("b", .ofNat 1 0)], [("a", .ofNat 1 1), ("b", .ofNat 1 0)],
   [("a", .ofNat 1 1), ("b", .ofNat 1 1)], [("a", .ofNat 1 0), ("b", .ofNat 1 1)],
   [("a", .ofNat 1 1), ("b", .ofNat 1 1)], [("a", LVec.xVec 1), ("b", .ofNat 1 1)],
   [("a", .ofNat 1 0), ("b", .ofNat 1 0)]]

def xprocRun (ch : Choice) : Option (List String) :=
  match exec xprocBits ch 50 (Config.init xprocBits xprocBits.initStore) with
  | .closed c => runYs xprocBits ch c xprocStim
  | _ => none

/-- `always_comb unique case (s) 2'd0: y = 1; 2'd0: y = 2; default: y = 3; endcase`: two arms
match `s = 0`, so the `unique` claim is violated there. -/
def uniqueDup : Elab where
  decls := #[{ name := "s", width := 2, isInput := true }, { name := "y", width := 2, isOutput := true }]
  procs := #[.comb (.caseStmt (.ident "s")
    #[.mk #[.lit (.ofNat 2 0)] (.blockingAssign (.ident "y") (.lit (.ofNat 2 1))),
      .mk #[.lit (.ofNat 2 0)] (.blockingAssign (.ident "y") (.lit (.ofNat 2 2)))]
    (some (.blockingAssign (.ident "y") (.lit (.ofNat 2 3)))) .normal .unique)]

def isRefused : ExecResult → Bool
  | .refused _ => true
  | _ => false

-- A violated `unique` claim refuses (s = 0: two arms match); a held one runs (s = 1: none
-- matches, the default runs).
#guard isRefused (exec uniqueDup σ_src 10
  (Config.init uniqueDup (uniqueDup.setName uniqueDup.initStore "s" (.ofNat 2 0))))
#guard showClosed uniqueDup ["y"] (exec uniqueDup σ_src 10
  (Config.init uniqueDup (uniqueDup.setName uniqueDup.initStore "s" (.ofNat 2 1)))) == some ["11"]

/-- `always_comb casez (s) 2'd1: y = 1; endcase`: a mode outside the profile. -/
def casezProbe : Elab where
  decls := uniqueDup.decls
  procs := #[.comb (.caseStmt (.ident "s")
    #[.mk #[.lit (.ofNat 2 1)] (.blockingAssign (.ident "y") (.lit (.ofNat 2 1)))] none .casez .none)]

-- `casez` refuses loudly; it never runs with plain-case meaning.
#guard isRefused (exec casezProbe σ_src 10
  (Config.init casezProbe (casezProbe.setName casezProbe.initStore "s" (.ofNat 2 1))))

-- The second block senses `t[0]` and nothing else of `t`.
#guard xprocBits.sens 1 == [.whole "b", .win "t" 0 1]
-- Xcelium's pinned trace: `y = {b, a}` at every cycle (cycles 1, 3, 5: `01`, `10`, `1x`).
#guard xprocRun σ_src == some ["00", "01", "11", "10", "11", "1x", "00"]
#guard xprocRun σ_rev == some ["00", "01", "11", "10", "11", "1x", "00"]

end Core0Smoke

/-! ## Axioms -/

#print axioms VType.width_conv
#print axioms VType.conv_of_four
#print axioms Choice.legal
#print axioms step_slotClosed
#print axioms exec_sound
#print axioms step_legal

end LeanModels.Sv.Kernel
