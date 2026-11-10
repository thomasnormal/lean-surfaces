import LeanModels.Sv.Sem2Ast

namespace LeanModels.Sv

/-! ## The fueled interpreter core -/

mutual

/-- Evaluate a semantic-tier expression (M0 discipline: fuel matched
first, decremented into every recursive call; both ternary arms evaluated;
loud on `unsupported` nodes reached). -/
def evalExpr2 (fuel : Nat) (st : SvState) (e : Expr2) : Res LVec :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match e with
    | .lit v => .ok v
    | .ident name => readSignal st name
    | .unary op a => do
        return evalUnaryOp op (← evalExpr2 fuel st a)
    | .resizeSigned width operand => do
        return (← evalExpr2 fuel st operand).resizeSigned width
    | .squash2 operand => do
        return (← evalExpr2 fuel st operand).toTwoState
    | .binary op l r => do
        let a ← evalExpr2 fuel st l
        let b ← evalExpr2 fuel st r
        return evalBinOp op a b
    | .scmp op l r => do
        let a ← evalExpr2 fuel st l
        let b ← evalExpr2 fuel st r
        match a.toInt?, b.toInt? with
        | some x, some y =>
            return .ofLogic (match op with
              | .lt => if x < y then .l1 else .l0
              | .le => if x ≤ y then .l1 else .l0
              | .gt => if x > y then .l1 else .l0
              | .ge => if x ≥ y then .l1 else .l0
              | _ => .lx)  -- non-order op: outside the constructor contract
        | _, _ => return .ofLogic .lx
    | .logical isAnd l r => do
        let a ← evalExpr2 fuel st l
        let b ← evalExpr2 fuel st r
        let res : Logic :=
          if isAnd then
            if a.isKnownZero || b.isKnownZero then .l0
            else if a.condTrue && b.condTrue then .l1
            else .lx
          else
            if a.condTrue || b.condTrue then .l1
            else if a.isKnownZero && b.isKnownZero then .l0
            else .lx
        return .ofLogic res
    | .ternary c t f => do
        let cv ← evalExpr2 fuel st c
        let tv ← evalExpr2 fuel st t
        let fv ← evalExpr2 fuel st f
        return LVec.ternary cv tv fv
    | .concat parts => do
        let vs ← evalExprs2 fuel st parts.toList
        return LVec.concatMany vs.toArray
    | .slice base lo w => do
        return (← evalExpr2 fuel st base).extract lo w
    | .index base idx elemW => do
        let bv ← evalExpr2 fuel st base
        let iv ← evalExpr2 fuel st idx
        match indexInt? idx iv with
        | some i =>
            if 0 ≤ i && (i + 1) * elemW ≤ bv.width then
              return bv.extract (i.toNat * elemW) elemW
            else
              return LVec.xVec elemW      -- out-of-range read: all-x (W05)
        | none => return LVec.xVec elemW  -- x/z index read: all-x (R02/R03/R05)
    | .repl n a => do
        return LVec.replVec n (← evalExpr2 fuel st a)
    | .reduce op a => do
        return .ofLogic (evalRedOp op (← evalExpr2 fuel st a))
    | .resize w a => do
        return (← evalExpr2 fuel st a).resizeU w
    | .unsupported svKind _ => .unsupported s!"unsupported expression '{svKind}'"

def evalExprs2 (fuel : Nat) (st : SvState) (es : List Expr2) : Res (List LVec) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match es with
    | [] => .ok []
    | e :: rest => do
        let v ← evalExpr2 fuel st e
        let vs ← evalExprs2 fuel st rest
        return v :: vs

/-- Resolve an assignment target to its write window `(name, lo, width)` —
`none` window = the pinned no-write case (x/z or out-of-range dynamic
index; the statement is still executed for its RHS side… M0 expressions are
pure, so "executed" just means the assignment is dropped). -/
def resolveLhs2 (fuel : Nat) (st : SvState) : Lhs2 → Res (String × Option (Nat × Nat))
  | .ident n => do
      match SvState.lookup st n with
      | some old => return (n, some (0, old.width))
      | none => .unsupported s!"unknown assignment target '{n}'"
  | .slice n lo w => .ok (n, some (lo, w))
  | .index n idx elemW => do
      let iv ← evalExpr2 fuel st idx
      match SvState.lookup st n with
      | none => .unsupported s!"unknown assignment target '{n}'"
      | some old =>
          match indexInt? idx iv with
          | some i =>
              if 0 ≤ i && (i + 1) * elemW ≤ old.width then
                return (n, some (i.toNat * elemW, elemW))
              else
                return (n, none)  -- OOB write: no-op (Z05)
          | none => return (n, none)  -- x/z-index write: no-op (W01/W03/W06/W08)
  | .concat _ => .unsupported "concatenated target requires continuous-assignment execution"

/-- Resolve every leaf of a continuous concatenation. The extractor only
emits concatenations whose leaves are direct, statically sized targets, but
the resolver still checks every leaf and rejects a dynamic no-write window:
continuous concatenation needs one sampled RHS and a definite destination
width for each slice. -/
def resolveConcatLhs2 (fuel : Nat) (st : SvState) : Lhs2 →
    Res (List (String × Nat × Nat))
  | .concat parts =>
      parts.foldlM (init := ([] : List (String × Nat × Nat)))
        (fun acc part => do
          let windows ← resolveConcatLhs2 fuel st part
          return acc ++ windows)
  | target => do
      let (name, window) ← resolveLhs2 fuel st target
      match window with
      | some (lo, width) => return [(name, lo, width)]
      | none => .unsupported "continuous concatenation target has no fixed window"

/-- Apply a sampled continuous-assignment RHS to concatenated leaves. LVec is
LSB-first, while a concatenation lists its leaves MSB-first, so the first
leaf receives the high slice and the remaining width decreases toward zero. -/
def writeConcatLhs2 (st : SvState) (value : LVec)
    (windows : List (String × Nat × Nat)) : Res SvState :=
  let total := windows.foldl (fun n (_, _, width) => n + width) 0
  let replacement := value.resizeU total
  let rec go (state : SvState) (remaining : List (String × Nat × Nat))
      (remainingWidth : Nat) : Res SvState :=
    match remaining with
    | [] => .ok state
    | (name, lo, width) :: rest =>
        match SvState.lookup state name with
        | none => .unsupported s!"unknown assign target '{name}'"
        | some old =>
            let nextWidth := remainingWidth - width
            let part := replacement.extract nextWidth width
            go (SvState.set state name (old.insertAt lo part)) rest nextWidth
  go st windows total

/-- Execute one statement (blocking hits the state via `insertAt`;
nonblocking enqueues the resolved window; `case` per `caseHit`, first
match, `default`, else no-op — check qualifiers do not alter execution). -/
def execStmt2 (fuel : Nat) (st : SvState) (nba : NbaQueue2) (stmt : Stmt2) :
    Res (SvState × NbaQueue2) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match stmt with
    | .blockingAssign target value => do
        let v ← evalExpr2 fuel st value
        match target with
        | .concat _ =>
            let windows ← resolveConcatLhs2 fuel st target
            let st' ← writeConcatLhs2 st v windows
            return (st', nba)
        | _ =>
            let (n, win) ← resolveLhs2 fuel st target
            match win with
            | none => return (st, nba)
            | some (lo, w) =>
                match SvState.lookup st n with
                | some old => return (SvState.set st n (old.insertAt lo (v.resizeU w)), nba)
                | none => .unsupported s!"unknown assignment target '{n}'"
    | .nbaAssign target value => do
        let v ← evalExpr2 fuel st value
        let (n, win) ← resolveLhs2 fuel st target
        match win with
        | none => return (st, nba)
        | some (lo, w) => return (st, nba ++ [(n, lo, v.resizeU w)])
    | .ifStmt cond thenBranch elseBranch => do
        let c ← evalExpr2 fuel st cond
        if c.condTrue then
          execStmt2 fuel st nba thenBranch
        else
          match elseBranch with
          | some s => execStmt2 fuel st nba s
          | none => .ok (st, nba)
    | .caseStmt subject items default? mode _check => do
        let sv ← evalExpr2 fuel st subject
        execCase2 fuel st nba sv items.toList default? mode
    | .block body => execStmts2 fuel st nba body.toList
    | .unsupported svKind _ => .unsupported s!"unsupported statement '{svKind}'"

/-- Walk the case items in source order; first hit executes; exhausted
items fall to `default` (no default: no-op — pin2a C05 / pin2b I09). -/
def execCase2 (fuel : Nat) (st : SvState) (nba : NbaQueue2) (subj : LVec) :
    List CaseItem2 → Option Stmt2 → CaseMode → Res (SvState × NbaQueue2)
  | [], default?, _ =>
      match fuel with
      | 0 => .timeout
      | fuel + 1 =>
          match default? with
          | some s => execStmt2 fuel st nba s
          | none => .ok (st, nba)
  | .mk pats body :: rest, default?, mode =>
      match fuel with
      | 0 => .timeout
      | fuel + 1 => do
          let pvs ← evalExprs2 fuel st pats.toList
          if pvs.any (fun pv => caseHit mode subj pv) then
            execStmt2 fuel st nba body
          else
            execCase2 fuel st nba subj rest default? mode


def execStmts2 (fuel : Nat) (st : SvState) (nba : NbaQueue2) (ss : List Stmt2) :
    Res (SvState × NbaQueue2) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match ss with
    | [] => .ok (st, nba)
    | s :: rest => do
        let (st', nba') ← execStmt2 fuel st nba s
        execStmts2 fuel st' nba' rest


end

def caseHitRows2 (fuel : Nat) (st : SvState) (subj : LVec) (mode : CaseMode) :
    List CaseItem2 → Res (List (Bool × Stmt2))
  | [] => .ok []
  | .mk pats body :: rest => do
      let pvs ← evalExprs2 fuel st pats.toList
      let rows ← caseHitRows2 fuel st subj mode rest
      return (pvs.any (fun pv => caseHit mode subj pv), body) :: rows

def checkCaseObligation (check : CaseCheck) (hasDefault : Bool)
    (hits : List (Bool × Stmt2)) : Res Unit :=
  let n := (hits.filter (·.1)).length
  match check with
  | .none => .ok ()
  | .unique => if n == 1 || (n == 0 && hasDefault) then .ok () else .unsupported "CaseCheck:unique"
  | .unique0 => if n ≤ 1 then .ok () else .unsupported "CaseCheck:unique0"
  | .priority => if n ≥ 1 || hasDefault then .ok () else .unsupported "CaseCheck:priority"

mutual
def validateCaseChecks2 (fuel : Nat) (st : SvState) (stmt : Stmt2) : Res Unit :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
      match stmt with
      | .blockingAssign _ _ | .nbaAssign _ _ | .unsupported _ _ => .ok ()
      | .ifStmt cond th el => do
          let cv ← evalExpr2 fuel st cond
          if cv.condTrue then validateCaseChecks2 fuel st th
          else match el with | some s => validateCaseChecks2 fuel st s | none => .ok ()
      | .block body => validateCaseChecksList2 fuel st body.toList
      | .caseStmt subj items dflt mode check => do
          let sv ← evalExpr2 fuel st subj
          let hits ← caseHitRows2 fuel st sv mode items.toList
          checkCaseObligation check dflt.isSome hits
          match hits.find? (·.1) with
          | some (_, body) => validateCaseChecks2 fuel st body
          | none => match dflt with | some s => validateCaseChecks2 fuel st s | none => .ok ()

def validateCaseChecksList2 (fuel : Nat) (st : SvState) (ss : List Stmt2) : Res Unit :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
      match ss with
      | [] => .ok ()
      | s :: rest => do
          validateCaseChecks2 fuel st s
          validateCaseChecksList2 fuel st rest
end

def validateProcessChecks2 (fuel : Nat) (st : SvState) : List Process2 → Res Unit
  | [] => .ok ()
  | p :: rest => do
      match p with
      | .alwaysComb body | .alwaysFF _ body | .alwaysPlain _ body
      | .alwaysFFR _ _ body _ =>
          if body.hasQualifiedCase then validateCaseChecks2 fuel st body else .ok ()
      | .assign _ _ | .unsupported _ _ => .ok ()
      validateProcessChecks2 fuel st rest

def validateBodyChecks2 (fuel : Nat) (st : SvState) (body : Stmt2) : Res Unit :=
  if body.hasQualifiedCase then validateCaseChecks2 fuel st body else .ok ()

/-! ## Comb settle -/

/-- Run one comb-phase process (continuous assigns may target selects —
partial drivers read-modify-write their slice; several assigns driving
disjoint slices of one signal settle to the union, undriven bits stay x). -/
def runCombProcess2 (fuel : Nat) (st : SvState) : Process2 → Res SvState
  | .assign target value => do
      let v ← evalExpr2 fuel st value
      match target with
      | .concat _ =>
          let windows ← resolveConcatLhs2 fuel st target
          writeConcatLhs2 st v windows
      | _ =>
          let (n, win) ← resolveLhs2 fuel st target
          match win with
          | none => .ok st
          | some (lo, w) =>
              match SvState.lookup st n with
              | some old => .ok (SvState.set st n (old.insertAt lo (v.resizeU w)))
              | none => .unsupported s!"unknown assign target '{n}'"
  | .alwaysComb body => do
      let (st', nba) ← execStmt2 fuel st [] body
      match nba with
      | [] => .ok st'
      | (name, _) :: _ =>
          .unsupported
            s!"nonblocking assignment to '{name}' inside always_comb is outside the cycle semantics"
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ _ => .ok st
  | .unsupported svKind _ => .unsupported s!"unsupported process '{svKind}'"

def combPass2 (d : Design2) (fuel : Nat) (st : SvState) : List Nat → Res SvState
  | [] => .ok st
  | i :: rest => do
      let st' ← match d.processes[i]? with
        | some p => runCombProcess2 fuel st p
        | none => pure st
      combPass2 d fuel st' rest

/-- σ-ordered settle passes to fixpoint, fuel-bounded (M0 discipline). -/
def combSettle2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (st : SvState)
    (k : Nat) : Res (SvState × Nat) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 => do
      let st' ← combPass2 d fuel st (σ.choose k d.combIndices)
      if st' == st then .ok (st', k + 1)
      else combSettle2 d σ fuel st' (k + 1)

/-! ## Reset-event phase -/

/-- Run one process at a reset event (only `alwaysFFR` bodies are ever
listed). The WHOLE body runs — on `rst_n: 1→x` the canonical
`if (!rst_n)` takes the else branch at the event (pin3 CYCLE 6). -/
def runResetProcess2 (fuel : Nat) (st : SvState) (nba : NbaQueue2) :
    Process2 → Res (SvState × NbaQueue2)
  | .alwaysFFR _ _ body _ => execStmt2 fuel st nba body
  | _ => .ok (st, nba)

def resetPass2 (d : Design2) (fuel : Nat) (st : SvState) (nba : NbaQueue2) :
    List Nat → Res (SvState × NbaQueue2)
  | [] => .ok (st, nba)
  | i :: rest => do
      let (st', nba') ← match d.processes[i]? with
        | some p => runResetProcess2 fuel st nba p
        | none => pure (st, nba)
      resetPass2 d fuel st' nba' rest

/-! ## Edge phase -/

def runEdgeProcess2 (fuel : Nat) (st : SvState) (nba : NbaQueue2) :
    Process2 → Res (SvState × NbaQueue2)
  | .alwaysFF _ body => execStmt2 fuel st nba body
  | .alwaysPlain _ body => execStmt2 fuel st nba body
  | .alwaysFFR _ _ body _ => execStmt2 fuel st nba body
  | .alwaysComb _ | .assign _ _ => .ok (st, nba)
  | .unsupported svKind _ => .unsupported s!"unsupported process '{svKind}'"

def edgePass2 (d : Design2) (fuel : Nat) (st : SvState) (nba : NbaQueue2) :
    List Nat → Res (SvState × NbaQueue2)
  | [] => .ok (st, nba)
  | i :: rest => do
      let (st', nba') ← match d.processes[i]? with
        | some p => runEdgeProcess2 fuel st nba p
        | none => pure (st, nba)
      edgePass2 d fuel st' nba' rest

/-! ## Admission guard for the one-clock `run2` profile

`cycleStep2` is deliberately the one-clock transport: one stimulus entry is
one rising edge.  The exact instant-list route in `MultiClock.lean` carries
independent and coincident clocks; letting a multi-clock design reach
`edgePass2` here would tick every domain on every entry and give a wrong
answer.  Retained data-driven event controls are likewise outside this
transport and remain a named clock boundary. -/

def run2Clock? : Process2 → Option String
  | .alwaysFF c _ | .alwaysPlain c _ | .alwaysFFR c _ _ _ => some c
  | _ => none

def run2ClockNames (d : Design2) : List String :=
  (d.processes.toList.filterMap run2Clock?).eraseDups

def run2ClockGuard (d : Design2) : Res Unit :=
  if (run2ClockNames d).length > 1 then
    .unsupported s!"Clock:multiple: module {d.name} has multiple edge clocks; run2 requires one clock per stimulus entry; use the exact MultiClock instant route"
  else if d.processes.toList.any (fun p =>
      match p with
      | .unsupported svKind _ => svKind.startsWith "SignalEventControl:"
      | _ => false) then
    .unsupported s!"Clock:implicit: module {d.name} has a data-driven event control; run2 has no event-sensitivity transport for it"
  else
    .ok ()

/-! ## The cycle -/

def applyInputs2 (d : Design2) (inputs : SvState) (st : SvState) : SvState :=
  d.decls.foldl
    (fun s declaration =>
      if declaration.isInput then
        match SvState.lookup inputs declaration.name with
        | some v => SvState.set s declaration.name
            (if declaration.twoState then v.toTwoState else v)
        | none => s
      else s)
    st

def initState2 (d : Design2) : SvState :=
  d.decls.toList.map fun dc =>
    let value := dc.init.getD (if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width)
    (dc.name, if dc.twoState then value.toTwoState else value)

/-- One clock cycle of the semantic tier — the M0 five sub-steps with the
reset-event phase inserted between the input settle and the posedge:

1. overwrite declared inputs from the stimulus;
2. comb settle;
3. **reset-event phase**: `alwaysFFR` bodies whose reset made a negedge
   (vs. the end of the previous cycle) run once in σ order, NBA committed,
   comb settled — reset values are visible to the posedge samplers (pin3);
4. edge phase: every posedge process runs once in σ order;
5. NBA commit; 6. comb settle. The result is the cycle's snapshot. -/
def cycleStep2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (inputs : SvState)
    (st : SvState) (k : Nat := 0) : Res (SvState × Nat) := do
  let st0 := applyInputs2 d inputs st
  let (st1, k1) ← combSettle2 d σ fuel st0 k
  let rdy := d.resetIndices st st1
  let (st2, k2) ←
    match rdy with
    | [] => pure (st1, k1)
    | _ => do
        let (str, nbar) ← resetPass2 d fuel st1 [] (σ.choose k1 rdy)
        combSettle2 d σ fuel (commitNba2 str nbar) (k1 + 1)
  let (st3, nba) ← edgePass2 d fuel st2 [] (σ.choose k2 d.edgeIndices)
  let st4 := commitNba2 st3 nba
  combSettle2 d σ fuel st4 (k2 + 1)

def runFrom2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (st : SvState)
    (k : Nat) : List SvState → Res (List SvState)
  | [] => .ok []
  | inputs :: rest => do
      let (st', k') ← cycleStep2 d σ fuel inputs st k
      let tr ← runFrom2 d σ fuel st' k' rest
      return st' :: tr

def validateTraceChecks2 (fuel : Nat) (d : Design2) : List SvState → Res Unit
  | [] => .ok ()
  | st :: rest => do
      validateProcessChecks2 fuel st d.processes.toList
      validateTraceChecks2 fuel d rest


/-- The semantic-tier entry point (M0 contract shape: startup from
declaration initializers, all else x; one snapshot per stimulus entry). -/
def run2 (d : Design2) (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
    Res (List SvState) :=
  do
    run2ClockGuard d
    let tr ← runFrom2 d σ fuel (initState2 d) 0 stim
    let _ ← if d.processes.toList.any Process2.hasQualifiedCase
      then validateTraceChecks2 fuel d tr else .ok ()
    return tr

/-! ## Execution-time qualified-case route

The historical `run2` entry point retains its completed-trace diagnostic for
backward compatibility.  `run2ExecChecks` is the exact E route for new rows:
it settles the input state, checks qualified claims on that pre-process state,
then delegates the actual scheduler step to the same `cycleStep2`.  Thus edge
claims are checked before their NBA commit; no second AST or scheduler is
introduced. -/

def cycleStep2ExecChecks (d : Design2) (σ : ScheduleOracle) (fuel : Nat)
    (inputs st : SvState) (k : Nat := 0) : Res (SvState × Nat) := do
  let st0 := applyInputs2 d inputs st
  let (settled, _) ← combSettle2 d σ fuel st0 k
  validateProcessChecks2 fuel settled d.processes.toList
  cycleStep2 d σ fuel inputs st k

def runFrom2ExecChecks (d : Design2) (σ : ScheduleOracle) (fuel : Nat)
    (st : SvState) (k : Nat) : List SvState → Res (List SvState)
  | [] => .ok []
  | inputs :: rest => do
      let (st', k') ← cycleStep2ExecChecks d σ fuel inputs st k
      let tr ← runFrom2ExecChecks d σ fuel st' k' rest
      return st' :: tr

def run2ExecChecks (d : Design2) (σ : ScheduleOracle) (fuel : Nat)
    (stim : List SvState) : Res (List SvState) :=
  do
    run2ClockGuard d
    runFrom2ExecChecks d σ fuel (initState2 d) 0 stim

/-! ## The pinned-fact table (`#guard` twins of the diff rows)

Row ids refer to the pin probes in the module docstring; every row was
green on Xcelium AND Icarus before the rule landed (case-inside rows:
Xcelium only — Icarus cannot parse the construct). -/

-- pin1 R01–R03: dynamic bit select; x/z index reads x.
private def v86 : LVec := .lit "10100110"
#guard evalExpr2 32 [] (.index (.lit v86) (.lit (.ofNat 3 2)) 1) == .ok (.lit "1")
#guard evalExpr2 32 [] (.index (.lit v86) (.lit (.lit "xxx")) 1) == .ok (.lit "x")
#guard evalExpr2 32 [] (.index (.lit v86) (.lit (.lit "01x")) 1) == .ok (.lit "x")

-- pin1 R04–R05: 2D element select m[i] = 8-bit chunk; x index → all-x.
private def m4x8 : LVec := .lit "10100001101100101100001111010100"  -- 32'hA1B2C3D4
#guard (evalExpr2 32 [] (.index (.lit m4x8) (.lit (.ofNat 2 3)) 8)).toOption.map
        LVec.toBinString == some "10100001"
#guard (evalExpr2 32 [] (.index (.lit m4x8) (.lit (.lit "xx")) 8)).toOption.map
        LVec.toBinString == some "xxxxxxxx"

-- pin2a W05: out-of-range dynamic read → x.
#guard (evalExpr2 32 [] (.index (.lit v86) (.lit (.ofNat 4 9)) 1)) == .ok (.lit "x")

-- pin1 R06: constant part select v[6:3].
#guard (evalExpr2 32 [] (.slice (.lit v86) 3 4)).toOption.map LVec.toBinString
        == some "0100"

-- pin1 R07 / pin4 Z06: replication.
#guard (evalExpr2 32 [] (.repl 3 (.lit (.lit "10")))).toOption.map LVec.toBinString
        == some "101010"
#guard (evalExpr2 32 [] (.repl 2 (.lit (.lit "1x")))).toOption.map LVec.toBinString
        == some "1x1x"

-- pin1 R08–R11, pin4 Z07: reductions.
#guard evalRedOp .or (.lit "00000000") == .l0
#guard evalRedOp .or (.lit "000x0000") == .lx
#guard evalRedOp .or (.lit "100x0000") == .l1
#guard evalRedOp .and (.lit "11111111") == .l1
#guard evalRedOp .and (.lit "11111110") == .l0
#guard evalRedOp .and (.lit "1111111x") == .lx
#guard evalRedOp .xor (.lit "10110000") == .l1
#guard evalRedOp .xor (.lit "1011000x") == .lx
#guard evalRedOp .nor (.lit "00000000") == .l1
#guard evalRedOp .nand (.lit "11111111") == .l0
#guard evalRedOp .or (.lit "zz") == .lx
#guard evalRedOp .and (.lit "zz") == .lx

-- pin4 S01–S05: signed comparison; $signed at equal width is bit identity.
#guard (evalExpr2 32 [] (.scmp .lt (.lit (.ofNat 8 0xFF)) (.lit (.ofNat 8 1))))
        == .ok (.lit "1")
#guard (evalExpr2 32 [] (.binary .lt (.lit (.ofNat 8 0xFF)) (.lit (.ofNat 8 1))))
        == .ok (.lit "0")
#guard (evalExpr2 32 [] (.scmp .ge (.lit (.ofNat 8 0xFF)) (.lit (.ofNat 8 1))))
        == .ok (.lit "0")
#guard (evalExpr2 32 [] (.scmp .lt (.lit (.ofNat 8 0x80)) (.lit (.ofNat 8 0x7F))))
        == .ok (.lit "1")
#guard (evalExpr2 32 [] (.scmp .lt (.lit (.lit "x1111111")) (.lit (.ofNat 8 0x7F))))
        == .ok (.lit "x")

-- pin5 L01–L12: logical && / || (definite-false/true short-outs, else x).
#guard evalExpr2 8 [] (.logical true (.lit (.lit "00")) (.lit (.lit "xx"))) == .ok (.lit "0")
#guard evalExpr2 8 [] (.logical true (.lit (.lit "xx")) (.lit (.lit "00"))) == .ok (.lit "0")
#guard evalExpr2 8 [] (.logical true (.lit (.lit "10")) (.lit (.lit "xx"))) == .ok (.lit "x")
#guard evalExpr2 8 [] (.logical true (.lit (.lit "10")) (.lit (.lit "01"))) == .ok (.lit "1")
#guard evalExpr2 8 [] (.logical true (.lit (.lit "0x")) (.lit (.lit "10"))) == .ok (.lit "x")
#guard evalExpr2 8 [] (.logical true (.lit (.lit "zz")) (.lit (.lit "10"))) == .ok (.lit "x")
#guard evalExpr2 8 [] (.logical false (.lit (.lit "10")) (.lit (.lit "xx"))) == .ok (.lit "1")
#guard evalExpr2 8 [] (.logical false (.lit (.lit "xx")) (.lit (.lit "01"))) == .ok (.lit "1")
#guard evalExpr2 8 [] (.logical false (.lit (.lit "00")) (.lit (.lit "00"))) == .ok (.lit "0")
#guard evalExpr2 8 [] (.logical false (.lit (.lit "xx")) (.lit (.lit "00"))) == .ok (.lit "x")

-- pin4 Z01–Z04: bitwise resize (zero-extend keeps x bits; truncate keeps
-- low bits) — never the arithmetic collapse.
#guard (LVec.resizeU (.lit "1010") 12).toBinString == "000000001010"
#guard (LVec.resizeU (.lit "10100101") 4).toBinString == "0101"
#guard (LVec.resizeU (.lit "x1x0") 12).toBinString == "00000000x1x0"
#guard (LVec.resizeU (.lit "1x000101") 4).toBinString == "0101"

-- pin2a W01/W02/W06/W08 + pin4 Z05: select writes (x/z/OOB index = no-op).
private def wrProbe (idx : String) : Res (SvState × NbaQueue2) :=
  execStmt2 32 [("v", LVec.ofNat 8 0x0F)] []
    (.blockingAssign (.index "v" (.lit (.lit idx)) 1) (.lit (.lit "1")))
#guard (wrProbe "xxx").toOption.map (fun (st, _) => SvState.showSignal st "v")
        == some "00001111"
#guard (wrProbe "110").toOption.map (fun (st, _) => SvState.showSignal st "v")
        == some "01001111"
#guard (wrProbe "zzz").toOption.map (fun (st, _) => SvState.showSignal st "v")
        == some "00001111"
#guard (wrProbe "1x0").toOption.map (fun (st, _) => SvState.showSignal st "v")
        == some "00001111"
#guard (execStmt2 32 [("v", LVec.ofNat 8 0x0F)] []
          (.blockingAssign (.index "v" (.lit (.ofNat 5 20)) 1) (.lit (.lit "1")))).toOption.map
        (fun (st, _) => SvState.showSignal st "v") == some "00001111"

-- pin2a W03/W04: element write via x index no-op; known index hits chunk.
#guard (execStmt2 32 [("m", LVec.lit "00010001001000100011001101000100")] []
          (.blockingAssign (.index "m" (.lit (.lit "xx")) 8) (.lit (.ofNat 8 0xFF)))).toOption.map
        (fun (st, _) => SvState.showSignal st "m")
        == some "00010001001000100011001101000100"
#guard (execStmt2 32 [("m", LVec.lit "00010001001000100011001101000100")] []
          (.blockingAssign (.index "m" (.lit (.ofNat 2 1)) 8) (.lit (.ofNat 8 0xFF)))).toOption.map
        (fun (st, _) => SvState.showSignal st "m")
        == some "00010001001000101111111101000100"

-- A procedural concatenation target uses the same fixed-window splitter as a
-- continuous assignment. Right streaming in the symbolic surface lowers to
-- this target shape, including a flattened fixed-array cell.
#guard (execStmt2 32 [("arr[0]", LVec.xVec 4), ("out", LVec.xVec 1)] []
          (.blockingAssign (.concat [.ident "arr[0]", .ident "out"])
            (.lit (.lit "10101")))).toOption.map
        (fun (st, _) => (SvState.showSignal st "arr[0]", SvState.showSignal st "out"))
        == some ("1010", "1")

-- pin2a C01–C05: plain case = case equality (x matches x); expression
-- labels; unique does not change execution (first match; no match+no
-- default = no-op).
private def oSet (v : Nat) : Stmt2 := .blockingAssign (.ident "o") (.lit (.ofNat 2 v))
private def caseProbe (subj : String) (items : Array CaseItem2)
    (dflt : Option Stmt2) (mode : CaseMode := .normal) : Option String :=
  (execStmt2 64 [("s", LVec.lit subj), ("o", LVec.xVec 2)] []
    (.caseStmt (.ident "s") items dflt mode .none)).toOption.map
    fun (st, _) => SvState.showSignal st "o"
#guard caseProbe "xx"
        #[.mk #[.lit (.lit "00")] (oSet 0), .mk #[.lit (.lit "xx")] (oSet 1)]
        (some (oSet 2))
        == some "01"
#guard caseProbe "0x"
        #[.mk #[.lit (.lit "00")] (oSet 0), .mk #[.lit (.lit "01")] (oSet 1)]
        (some (oSet 3))
        == some "11"
-- fifo style: case (1'b1) with signal labels, first match wins.
#guard (execStmt2 64 [("s", LVec.lit "11"), ("p", LVec.xVec 3)] []
          (.caseStmt (.lit (.lit "1"))
            #[.mk #[.index (.ident "s") (.lit (.ofNat 1 0)) 1]
                (.blockingAssign (.ident "p") (.lit (.ofNat 3 1))),
              .mk #[.index (.ident "s") (.lit (.ofNat 1 1)) 1]
                (.blockingAssign (.ident "p") (.lit (.ofNat 3 2)))]
            (some (.blockingAssign (.ident "p") (.lit (.ofNat 3 7)))) .normal .unique)).toOption.map
        (fun (st, _) => SvState.showSignal st "p") == some "001"
#guard (execStmt2 64 [("s", LVec.lit "00"), ("p", LVec.ofNat 3 5)] []
          (.caseStmt (.lit (.lit "1"))
            #[.mk #[.index (.ident "s") (.lit (.ofNat 1 0)) 1]
                (.blockingAssign (.ident "p") (.lit (.ofNat 3 1))),
              .mk #[.index (.ident "s") (.lit (.ofNat 1 1)) 1]
                (.blockingAssign (.ident "p") (.lit (.ofNat 3 2)))]
            none .normal .unique)).toOption.map
        (fun (st, _) => SvState.showSignal st "p") == some "101"

-- pin2b I01–I09: case inside (wildcard match, item-side don't-cares;
-- subject x in a cared position falls through; comma lists).
#guard caseProbe "10"
        #[.mk #[.lit (.lit "0z")] (oSet 0), .mk #[.lit (.lit "1z")] (oSet 1)]
        (some (oSet 2)) .inside == some "01"
#guard caseProbe "0x"
        #[.mk #[.lit (.lit "00")] (oSet 0), .mk #[.lit (.lit "01")] (oSet 1)]
        (some (oSet 2)) .inside == some "10"
#guard caseProbe "1x"
        #[.mk #[.lit (.lit "0z")] (oSet 0), .mk #[.lit (.lit "1z")] (oSet 1)]
        (some (oSet 2)) .inside == some "01"
#guard caseProbe "10"
        #[.mk #[.lit (.lit "1x")] (oSet 1)]
        (some (oSet 2)) .inside == some "01"
#guard caseProbe "01"
        #[.mk #[.lit (.lit "00"), .lit (.lit "01")] (oSet 0)]
        (some (oSet 2)) .inside == some "00"
#guard caseProbe "z0"
        #[.mk #[.lit (.lit "00")] (oSet 0), .mk #[.lit (.lit "10")] (oSet 1)]
        (some (oSet 2)) .inside == some "10"
#guard caseProbe "x1"
        #[.mk #[.lit (.lit "z1")] (oSet 1)]
        (some (oSet 2)) .inside == some "01"

-- pin3: the async-reset design, all 8 pinned cycles (see the docstring's
-- reset ledger). Model of rows/pin3.sv `ar`.
private def arDesign : Design2 :=
  { name := "ar"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "rst_n", width := 1, isInput := true },
      { name := "d", width := 4, isInput := true },
      { name := "q", width := 4, isOutput := true },
      { name := "q2", width := 4, isOutput := true }]
    processes := #[
      @Process2.alwaysFFR "clk" "rst_n"
        (.ifStmt (.unary .bnot (.ident "rst_n"))
          (.nbaAssign (.ident "q") (.lit (.ofNat 4 0)))
          (some (.nbaAssign (.ident "q") (.ident "d")))) false,
      .alwaysFF "clk" (.nbaAssign (.ident "q2") (.ident "q"))] }

private def arStim : List SvState := [
  [("rst_n", LVec.lit "0"), ("d", LVec.ofNat 4 5)],
  [("rst_n", LVec.lit "1"), ("d", LVec.ofNat 4 5)],
  [("d", LVec.ofNat 4 7)],
  [("rst_n", LVec.lit "0"), ("d", LVec.ofNat 4 9)],
  [("d", LVec.ofNat 4 3)],
  [("rst_n", LVec.lit "1")],
  [("rst_n", LVec.lit "x"), ("d", LVec.ofNat 4 6)],
  [("rst_n", LVec.lit "1"), ("d", LVec.ofNat 4 2)]]

#guard (Res.toOption (run2 arDesign σ_src 64 arStim)).map
        (fun tr => tr.map fun st =>
          (SvState.showSignal st "q", SvState.showSignal st "q2"))
      == some [
        ("0000", "0000"),  -- c0: x→0 negedge resets pre-edge; q2 samples 0
        ("0101", "0000"),  -- c1: release; q2 samples pre-edge q
        ("0111", "0101"),  -- c2
        ("0000", "0000"),  -- c3: 1→0 negedge — reset visible to q2 SAME cycle
        ("0000", "0000"),  -- c4: held low: posedge reset branch holds
        ("0011", "0000"),  -- c5: deassert = posedge of rst_n, no event
        ("0110", "0110"),  -- c6: 1→x negedge runs ELSE branch pre-edge!
        ("0010", "0110")]  -- c7: x→1 = posedge, no event

-- Reset phase and edge phase both fire for a held-low reset with data
-- changing (the level-idempotence half of the ledger): q stays 0.
#guard (Res.toOption (run2 arDesign σ_src 64
        [[("rst_n", LVec.lit "0"), ("d", LVec.ofNat 4 5)],
         [("d", LVec.ofNat 4 9)], [("d", LVec.ofNat 4 1)]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "q")
      == some ["0000", "0000", "0000"]

-- Partial continuous drivers (ff_one shape): two assigns drive disjoint
-- bits of one net; undriven bits stay x.
private def partialDrv : Design2 :=
  { name := "pd"
    decls := #[
      { name := "a", width := 2, isInput := true },
      { name := "y", width := 4 }]
    processes := #[
      .assign (.slice "y" 0 1) (.index (.ident "a") (.lit (.ofNat 1 0)) 1),
      .assign (.slice "y" 2 1) (.index (.ident "a") (.lit (.ofNat 1 1)) 1)] }

#guard (Res.toOption (run2 partialDrv σ_src 64 [[("a", LVec.lit "11")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "y")
      == some ["x1x1"]

-- A concatenated continuous driver samples one source vector and distributes
-- its MSB-first leaves to the existing packed windows.
private def concatDrv : Design2 :=
  { name := "concat_drv"
    decls := #[
      { name := "source", width := 8, isInput := true },
      { name := "upper", width := 4 },
      { name := "lower", width := 4 }]
    processes := #[
      .assign (.concat [.ident "upper", .ident "lower"]) (.ident "source")] }

#guard (Res.toOption (run2 concatDrv σ_src 64
        [[("source", LVec.lit "00111100")],
         [("source", LVec.lit "10100101")],
         [("source", LVec.lit "xxxx0000")]])).map
        (fun tr => tr.map fun st =>
          (SvState.showSignal st "upper", SvState.showSignal st "lower"))
      == some [("0011", "1100"), ("1010", "0101"), ("xxxx", "0000")]

end LeanModels.Sv
