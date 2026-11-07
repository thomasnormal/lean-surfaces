import LeanModels.Sv.Gen2
import LeanModels.Sv.Kernel.MemProc

/-!
# Source-shaped memory cycle adapter

This is the provisional `run2` view for the first sequential memory rung.  A
one-rank unpacked declaration remains a `PDecl`, and a selected cell remains
`PExpr.arrayElem`/`PLhs.arrayElem`; the adapter never expands a parameter-sized
array into default-point scalar declarations.  `MemState` is the only storage
for those cells.  The ordinary `Design2`/`SvState` route stays unchanged for
designs without memories.

The adapter deliberately admits the small FIFO shape needed by the frontier
packet: scalar conditions and RHSs, direct cell reads, scalar or cell NBA
targets, one async reset, and continuous scalar assigns from a cell.  Loops,
compound memory expressions, partial targets, and hierarchy remain named
refusals.  Its `fuel` argument is the existing run2 executor fuel; it is not a
meaning parameter or a memory-size cap.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

structure MemDesign2 where
  name : String
  env : IEnv
  decls : List Decl
  memDecls : List PDecl
  processes : List PProcess
deriving Repr, Inhabited

structure MemCycleState where
  scalar : SvState
  memory : MemState
deriving Inhabited

abbrev MemScalarNba := NbaQueue2
abbrev MemPending := MemScalarNba × MemNba

def memDeclOf? : List PDecl → String → Option PDecl
  | [], _ => none
  | d :: ds, n => if d.name == n then some d else memDeclOf? ds n

def memDeclsOf (d : PDesign) : List PDecl :=
  d.decls.filter fun pd => !pd.unpackedDims.isEmpty

/-! ## Generate labels

Generate bodies keep their source `PProcess` until this adapter is
instantiated.  Substituting a concrete genvar label here is deliberately
structural: the resulting `PExpr.arrayElem` remains a memory cell, rather
than becoming a default-point scalar declaration. -/

def memSubstExpr (vals : List (String × Int)) : PExpr → PExpr
  | .genvarRef n =>
      match vals.lookup n with
      | some v => .int v
      | none => .genvarRef n
  | .unary op a => .unary op (memSubstExpr vals a)
  | .binary op a b => .binary op (memSubstExpr vals a) (memSubstExpr vals b)
  | .ternary c a b => .ternary (memSubstExpr vals c) (memSubstExpr vals a)
      (memSubstExpr vals b)
  | .concat xs => .concat (xs.map (memSubstExpr vals))
  | .resize w a => .resize w (memSubstExpr vals a)
  | .signedResize w a => .signedResize w (memSubstExpr vals a)
  | .squash2 w a => .squash2 w (memSubstExpr vals a)
  | .sysCall fn a => .sysCall fn (memSubstExpr vals a)
  | .bitSel a b => .bitSel (memSubstExpr vals a) (memSubstExpr vals b)
  | .partSel a b c => .partSel (memSubstExpr vals a) (memSubstExpr vals b)
      (memSubstExpr vals c)
  | .repl a b => .repl (memSubstExpr vals a) (memSubstExpr vals b)
  | .reduce op a => .reduce op (memSubstExpr vals a)
  | .cast s a => .cast s (memSubstExpr vals a)
  | .arrayElem n xs => .arrayElem n (xs.map (memSubstExpr vals))
  | .arrayPart n xs mode a b => .arrayPart n (xs.map (memSubstExpr vals)) mode
      (memSubstExpr vals a) (memSubstExpr vals b)
  | e => e

def memSubstLhs (vals : List (String × Int)) : PLhs → PLhs
  | .bitSel n i => .bitSel n (memSubstExpr vals i)
  | .partSel n a b => .partSel n (memSubstExpr vals a) (memSubstExpr vals b)
  | .concat xs => .concat (xs.map (memSubstLhs vals))
  | .arrayElem n xs => .arrayElem n (xs.map (memSubstExpr vals))
  | .arrayPart n xs mode a b => .arrayPart n (xs.map (memSubstExpr vals)) mode
      (memSubstExpr vals a) (memSubstExpr vals b)
  | l => l

mutual
def memSubstStmt (vals : List (String × Int)) : PStmt → PStmt
  | .blockingAssign n e => .blockingAssign n (memSubstExpr vals e)
  | .nbaAssign n e => .nbaAssign n (memSubstExpr vals e)
  | .ifStmt c t e => .ifStmt (memSubstExpr vals c) (memSubstStmt vals t)
      (memSubstStmtOpt vals e)
  | .block xs => .block (memSubstStmtList vals xs)
  | .forLoop n i c s b => .forLoop n (memSubstExpr vals i) (memSubstExpr vals c)
      (memSubstExpr vals s) (memSubstStmt vals b)
  | .blockingAssignL l e => .blockingAssignL (memSubstLhs vals l) (memSubstExpr vals e)
  | .nbaAssignL l e => .nbaAssignL (memSubstLhs vals l) (memSubstExpr vals e)
  | .caseStmt s items d mode check =>
      .caseStmt (memSubstExpr vals s)
        (memSubstCaseItems vals items) (memSubstStmtOpt vals d) mode check
  | s => s
termination_by structural s => s

def memSubstStmtOpt (vals : List (String × Int)) : Option PStmt → Option PStmt
  | none => none
  | some s => some (memSubstStmt vals s)
termination_by structural o => o

def memSubstStmtList (vals : List (String × Int)) : List PStmt → List PStmt
  | [] => []
  | s :: ss => memSubstStmt vals s :: memSubstStmtList vals ss
termination_by structural xs => xs

def memSubstCaseItems (vals : List (String × Int)) :
    List (List PExpr × PStmt) → List (List PExpr × PStmt)
  | [] => []
  | (ps, b) :: rest =>
      (ps.map (memSubstExpr vals), memSubstStmt vals b) :: memSubstCaseItems vals rest
termination_by structural xs => xs

def memSubstProcess (vals : List (String × Int)) : PProcess → PProcess
  | .alwaysFF c b => .alwaysFF c (memSubstStmt vals b)
  | .alwaysPlain c b => .alwaysPlain c (memSubstStmt vals b)
  | .alwaysComb b => .alwaysComb (memSubstStmt vals b)
  | .assign n e => .assign n (memSubstExpr vals e)
  | .assignL l e => .assignL (memSubstLhs vals l) (memSubstExpr vals e)
  | .alwaysFFR c r b h => .alwaysFFR c r (memSubstStmt vals b) h
  | p => p
termination_by structural p => p
end

def memBindVals (env : IEnv) (vals : List (String × Int)) : IEnv :=
  vals.foldl (fun e (n, v) => e.bindVal n v) env

mutual
def memExpandItem (env : IEnv) (iterFuel : Nat) (vals : List (String × Int)) :
    GenItem → Res (List PProcess)
  | .process p => .ok [memSubstProcess vals p]
  | .unsupported k t => .ok [.unsupported k t]
  | .inst i => .ok [.unsupported "Instance"
      s!"module instance '{i.name}' of '{i.module}' outside the memory cycle route"]
  | .genIf cond thenB elseB =>
      match evalGenGuard (memBindVals env vals) cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v => if v != 0 then memExpandList env iterFuel vals thenB
                 else memExpandList env iterFuel vals elseB
  | .genFor _label g initE bound step _rc body =>
      let env' := memBindVals env vals
      match evalInt env' initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env' g bound δ iterFuel i0
          memExpandIters env iterFuel vals g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)

def memExpandList (env : IEnv) (iterFuel : Nat) (vals : List (String × Int)) :
    List GenItem → Res (List PProcess)
  | [] => .ok []
  | it :: rest => do
      let ps ← memExpandItem env iterFuel vals it
      let qs ← memExpandList env iterFuel vals rest
      .ok (ps ++ qs)
  termination_by xs => (sizeOf xs, 0)

def memExpandIters (env : IEnv) (iterFuel : Nat) (vals : List (String × Int))
    (g : String) : List Int → List GenItem → Res (List PProcess)
  | [], _ => .ok []
  | v :: vs, body => do
      let ps ← memExpandList env iterFuel ((g, v) :: vals) body
      let qs ← memExpandIters env iterFuel vals g vs body
      .ok (ps ++ qs)
  termination_by vs body => (sizeOf body, vs.length)
end

def scalarDeclsMem (env : IEnv) : List PDecl → Res (List Decl)
  | [] => .ok []
  | pd :: rest =>
      match pd.type.width env with
      | .error e => .unsupported s!"decl '{pd.name}': {e}"
      | .ok w =>
          let env' := { env with widths := (pd.name, w) :: env.widths }
          if !pd.unpackedDims.isEmpty then
            match pd.memShape? env with
            | .error e => .unsupported e
            | .ok _ => scalarDeclsMem env' rest
          else
            match instDecl env pd with
            | .unsupported e => .unsupported e
            | .timeout => .timeout
            | .ok dc =>
                match scalarDeclsMem env' rest with
                | .ok ds => .ok (dc :: ds)
                | .unsupported e => .unsupported e
                | .timeout => .timeout

def instantiateMem2 (d : PDesign) (args : List Int)
    (iterFuel : Nat := 4096) : Res MemDesign2 := do
  if args.length != d.params.length then
    .unsupported s!"parameter arity: got {args.length}, want {d.params.length}"
  let env ← d.paramEnv2 args
  if !d.others.isEmpty then
    .unsupported "memory cycle route does not yet admit unsupported module members"
  let decls ← scalarDeclsMem env d.decls
  let generated ← memExpandList env iterFuel [] d.generates
  let envP := { env with widths := decls.map fun dc => (dc.name, dc.width) }
  return { name := d.name, env := envP, decls, memDecls := memDeclsOf d,
           processes := d.processes ++ generated }

def instantiateMemD2 (d : PDesign) (args : List Int) : MemDesign2 :=
  match instantiateMem2 d args (PDesign.surfaceFuel args) with
  | .ok m => m
  | .timeout =>
      { name := d.name, env := {}, decls := [], memDecls := [], processes :=
          [.unsupported "Instantiate" "memory cycle route exhausted executor fuel"] }
  | .unsupported msg =>
      { name := d.name, env := {}, decls := [], memDecls := [], processes :=
          [.unsupported "Instantiate" msg] }

def MemDesign2.initState (d : MemDesign2) : MemCycleState :=
  { scalar := d.decls.map fun dc =>
      let value := dc.init.getD (if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width)
      (dc.name, if dc.twoState then value.toTwoState else value)
    memory := MemState.ofShapes ((d.memDecls.map fun pd =>
      match pd.memShape? d.env with
      | .ok (some shape) => shape
      | _ => { name := pd.name, elemWidth := 0, msb := 0, lsb := 0 })) }

def MemDesign2.applyInputs (d : MemDesign2) (inputs : SvState)
    (st : MemCycleState) : MemCycleState :=
  { st with scalar :=
      d.decls.foldl (fun s dc =>
        if dc.isInput then
          match SvState.lookup inputs dc.name with
          | some v => SvState.set s dc.name
              (if dc.twoState then v.toTwoState else v)
          | none => s
        else s) st.scalar }

mutual
def memExprReadsArray : PExpr → Bool
  | .arrayElem .. | .arrayPart .. => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => memExprReadsArray a
  | .binary _ a b | .bitSel a b | .repl a b => memExprReadsArray a || memExprReadsArray b
  | .partSel a b c | .ternary a b c =>
      memExprReadsArray a || memExprReadsArray b || memExprReadsArray c
  | .concat xs => memExprReadsArrayList xs
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .fill _ | .unsupported .. => false

def memExprReadsArrayList : List PExpr → Bool
  | [] => false
  | x :: xs => memExprReadsArray x || memExprReadsArrayList xs
end

/-! ## Runtime memory indices

The source-shaped memory route keeps a dynamic unpacked selector as a cell
operation.  Constant selectors still use the elaboration-time path from
`MemElab`; a signal-valued selector is evaluated against the scalar state at
issue time.  An unknown index reads `x` and drops a write, while an integer
outside the declared range gets the `MemBlock` x/no-op behavior. -/

def evalMemIndex (d : MemDesign2) (fuel : Nat) (st : MemCycleState)
    (idx : PExpr) : Res (Option Int) :=
  match evalInt d.env idx with
  | .ok i => .ok (some i)
  | .error _ =>
      let idx2 := instIndex2 d.env [] idx
      match evalExpr2 fuel st.scalar idx2 with
      | .ok v => .ok (indexInt? idx2 v)
      | .timeout => .timeout
      | .unsupported e => .unsupported s!"memory index: {e}"

def evalMemCell (d : MemDesign2) (fuel : Nat) (st : MemCycleState)
    (pd : PDecl) (indices : List PExpr) : Res LVec := do
  match pd.memShape? d.env with
  | .error e => .unsupported e
  | .ok none => .unsupported s!"memory RHS '{pd.name}' is not a cell"
  | .ok (some shape) =>
      match indices with
      | [idx] =>
          let k ← evalMemIndex d fuel st idx
          match k with
          | none => .ok (LVec.xVec shape.elemWidth)
          | some i =>
              match st.memory.read shape.name i with
              | some v => .ok v
              | none => .unsupported s!"memory '{shape.name}' is not present in E state"
      | _ => .unsupported s!"memory RHS '{pd.name}' has rank outside the one-cell fragment"

def resolveMemTarget (d : MemDesign2) (fuel : Nat) (st : MemCycleState)
    (pd : PDecl) (target : PLhs) : Res (Option PLhs) :=
  match target with
  | .arrayElem n [idx] =>
      if n != pd.name then
        .unsupported s!"array target '{n}' does not name declaration '{pd.name}'"
      else
        match evalInt d.env idx with
        | .ok _ => .ok (some target)
        | .error _ =>
            match evalMemIndex d fuel st idx with
            | .ok none => .ok none
            | .ok (some i) => .ok (some (.arrayElem n [.int i]))
            | .timeout => .timeout
            | .unsupported e => .unsupported e
  | .arrayElem n _ =>
      .unsupported s!"array target '{n}' has rank outside the one-cell fragment"
  | _ => .unsupported s!"target '{pd.name}' is not an unpacked array element"

def evalMemExpr (d : MemDesign2) (fuel : Nat) (st : MemCycleState)
    (ctx : Option Nat) (e : PExpr) : Res LVec :=
  match e with
  | .arrayElem n is =>
      match memDeclOf? d.memDecls n with
      | none => .unsupported s!"memory RHS '{n}' is not declared"
      | some pd =>
          evalMemCell d fuel st pd is
  | .arrayPart .. => .unsupported "memory RHS partial target is outside the one-cell fragment"
  | _ =>
      if memExprReadsArray e then
        .unsupported "memory expression is not a direct cell read"
      else
        evalExpr2 fuel st.scalar (instExpr2 d.env [] ctx e)

def updateScalarBlocking (st : MemCycleState) (target : Lhs2) (v : LVec) : Res MemCycleState :=
  match resolveLhs2 1 st.scalar target with
  | .unsupported msg => .unsupported msg
  | .timeout => .timeout
  | .ok (_, none) => .ok st
  | .ok (n, some (lo, w)) =>
      match SvState.lookup st.scalar n with
      | none => .unsupported s!"unknown assignment target '{n}'"
      | some old => .ok { st with scalar := SvState.set st.scalar n (old.insertAt lo (v.resizeU w)) }

def enqueueScalarNba (st : MemCycleState) (q : MemPending) (target : Lhs2) (v : LVec) : Res MemPending :=
  match resolveLhs2 1 st.scalar target with
  | .unsupported msg => .unsupported msg
  | .timeout => .timeout
  | .ok (_, none) => .ok q
  | .ok (n, some (lo, w)) => .ok (q.1 ++ [(n, lo, v.resizeU w)], q.2)

def commitMemPending (d : MemDesign2) (st : MemCycleState) (q : MemPending) : Res MemCycleState := do
  let scalar := commitNba2 st.scalar q.1
  let memory ← commitMemNba d.env st.memory q.2
  return { scalar, memory }

mutual
def execMemStmt (d : MemDesign2) (fuel : Nat) (st : MemCycleState)
    (q : MemPending) : PStmt → Res (MemCycleState × MemPending)
  | .blockingAssign n e => do
      let v ← evalMemExpr d fuel st (d.env.widths.lookup n) e
      let st' ← updateScalarBlocking st (.ident n) v
      return (st', q)
  | .nbaAssign n e => do
      let v ← evalMemExpr d fuel st (d.env.widths.lookup n) e
      let q' ← enqueueScalarNba st q (.ident n) v
      return (st, q')
  | .blockingAssignL lhs e =>
      match lhs with
      | .arrayElem n _ => do
          let some pd := memDeclOf? d.memDecls n
            | .unsupported s!"memory target '{n}' is not declared"
          let target? ← resolveMemTarget d fuel st pd lhs
          match target? with
          | none => .ok (st, q)
          | some target =>
              let v ← evalMemExpr d fuel st (pd.type.width d.env |>.toOption) e
              match MemState.writeTarget d.env pd target v st.memory with
              | .error msg => .unsupported s!"memory blocking write: {msg}"
              | .ok none => .unsupported s!"memory blocking write '{n}' did not find its state"
              | .ok (some memory) => .ok ({ st with memory }, q)
      | _ => do
          let some (l2, w) := (instLhs2 d.env [] lhs).toOption
            | .unsupported "memory scalar target is outside the admitted fragment"
          let v ← evalMemExpr d fuel st (some w) e
          let st' ← updateScalarBlocking st l2 v
          return (st', q)
  | .nbaAssignL lhs e =>
      match lhs with
      | .arrayElem n _ => do
          let some pd := memDeclOf? d.memDecls n
            | .unsupported s!"memory target '{n}' is not declared"
          let target? ← resolveMemTarget d fuel st pd lhs
          match target? with
          | none => .ok (st, q)
          | some target =>
              let value ← evalMemExpr d fuel st (pd.type.width d.env |>.toOption) e
              match enqueueMemNba d.env pd target value q.2 with
              | .error msg => .unsupported s!"memory NBA enqueue: {msg}"
              | .ok q' => .ok (st, (q.1, q'))
      | _ => do
          let some (l2, w) := (instLhs2 d.env [] lhs).toOption
            | .unsupported "memory scalar target is outside the admitted fragment"
          let v ← evalMemExpr d fuel st (some w) e
          let q' ← enqueueScalarNba st q l2 v
          return (st, q')
  | .ifStmt c th el => do
      let cv ← evalMemExpr d fuel st none c
      if cv.condTrue then execMemStmt d fuel st q th
      else match el with | some s => execMemStmt d fuel st q s | none => .ok (st, q)
  | .block body => execMemStmts d fuel st q body
  | .forLoop .. => .unsupported "ForLoopStatement:memory cycle route"
  | .caseStmt .. => .unsupported "CaseStatement:memory cycle route"
  | .unsupported k t => .unsupported s!"{k}: {t}"

def execMemStmts (d : MemDesign2) (fuel : Nat) (st : MemCycleState)
    (q : MemPending) : List PStmt → Res (MemCycleState × MemPending)
  | [] => .ok (st, q)
  | s :: rest => do
      let (st', q') ← execMemStmt d fuel st q s
      execMemStmts d fuel st' q' rest
end

def runMemProcess (d : MemDesign2) (fuel : Nat) (st : MemCycleState)
    (q : MemPending) : PProcess → Res (MemCycleState × MemPending)
  | .alwaysFF _ body | .alwaysPlain _ body | .alwaysFFR _ _ body _ =>
      execMemStmt d fuel st q body
  | .alwaysComb body => execMemStmt d fuel st q body
  | .assign target e => do
      let v ← evalMemExpr d fuel st (d.env.widths.lookup target) e
      let some dc := d.decls.find? (·.name == target)
        | .unsupported s!"assign target '{target}' is not declared"
      let old ← match SvState.lookup st.scalar target with
        | some v => .ok v
        | none => .unsupported s!"assign target '{target}' is not present"
      .ok ({ st with scalar := SvState.set st.scalar target (old.insertAt 0 (v.resizeU dc.width)) }, q)
  | .assignL _ _ => .unsupported "AssignL:memory cycle route"
  | .unsupported k t => .unsupported s!"{k}: {t}"

def memClockFires (prev cur : SvState) (clock : String) : Bool :=
  isPosedge (SvState.bit0 prev clock) (SvState.bit0 cur clock)

def memResetFires (prev cur : SvState) (rstn : String) (resetHigh : Bool) : Bool :=
  if resetHigh then
    isPosedge (SvState.bit0 prev rstn) (SvState.bit0 cur rstn)
  else
    isNegedge (SvState.bit0 prev rstn) (SvState.bit0 cur rstn)

def memStep (d : MemDesign2) (fuel : Nat) (inputs : SvState)
    (prev : MemCycleState) : Res MemCycleState := do
  let st0 := d.applyInputs inputs prev
  let q0 : MemPending := ([], [])
  let (st1, q1) ← if d.processes.any (fun p =>
      match p with
      | .alwaysFFR _ rst _ high => memResetFires prev.scalar st0.scalar rst high
      | _ => false) then
      d.processes.foldlM (init := (st0, q0)) fun acc p =>
        match p with
        | .alwaysFFR _ rst _ high =>
            if memResetFires prev.scalar st0.scalar rst high then
              runMemProcess d fuel acc.1 acc.2 p
            else .ok acc
        | _ => .ok acc
    else .ok (st0, q0)
  let st1 ← commitMemPending d st1 q1
  let (st2, q2) ← d.processes.foldlM (init := (st1, ([], []))) fun acc p =>
    match p with
    | .alwaysFF clock _ | .alwaysPlain clock _ =>
        if memClockFires prev.scalar st0.scalar clock then
          runMemProcess d fuel acc.1 acc.2 p
        else .ok acc
    | .alwaysFFR clock rst _ high =>
        -- A simultaneous reset and clock event is one source event.  The
        -- reset phase above has already run the body, so do not run it again
        -- in the edge phase.
        if memClockFires prev.scalar st0.scalar clock &&
            !memResetFires prev.scalar st0.scalar rst high then
          runMemProcess d fuel acc.1 acc.2 p
        else .ok acc
    | _ => .ok acc
  let st2 ← commitMemPending d st2 q2
  d.processes.foldlM (init := st2) fun st p =>
    match p with
    | .assign target e =>
        match d.decls.find? (·.name == target) with
        | none => .unsupported s!"assign target '{target}' is not declared"
        | some dc =>
            match SvState.lookup st.scalar target with
            | none => .unsupported s!"assign target '{target}' is not present"
            | some old => do
                let v ← evalMemExpr d fuel st (some dc.width) e
                let scalar := SvState.set st.scalar target
                  (old.insertAt 0 (v.resizeU dc.width))
                return { st with scalar }
    | .alwaysComb _ =>
        match runMemProcess d fuel st ([], []) p with
        | .ok (st', ([], [])) => .ok st'
        | .ok (_, _) => .unsupported "AlwaysComb:memory cycle route does not admit NBA"
        | .unsupported e => .unsupported e
        | .timeout => .timeout
    | _ => .ok st

def runMemFrom (d : MemDesign2) (fuel : Nat) (st : MemCycleState)
    (stim : List SvState) : Res (List SvState) :=
  match stim with
  | [] => .ok []
  | input :: rest => do
      let st' ← memStep d fuel input st
      let tr ← runMemFrom d fuel st' rest
      return st'.scalar :: tr

def runMem2 (d : MemDesign2) (fuel : Nat) (stim : List SvState) : Res (List SvState) :=
  runMemFrom d fuel d.initState stim

private def memProbeDecl : PDecl :=
  { name := "mem", type := .packed [⟨.int 7, .int 0⟩] (some 8),
    unpackedDims := [⟨.int 0, .int 3⟩] }

private def memProbeDesign : MemDesign2 :=
  { name := "probe", env := { widths := [("q", 8), ("d", 8), ("rstn", 1), ("clk", 1)] },
    decls := [
      { name := "clk", width := 1, isInput := true },
      { name := "rstn", width := 1, isInput := true },
      { name := "d", width := 8, isInput := true },
      { name := "q", width := 8, isOutput := true }],
    memDecls := [memProbeDecl], processes := [] }

#guard (MemState.read memProbeDesign.initState.memory "mem" 0).isSome
#guard runMem2 memProbeDesign 8 [] == .ok []

end LeanModels.Sv.Kernel

#print axioms LeanModels.Sv.Kernel.runMem2

namespace LeanModels.Sv

open Kernel

def PDesign.instantiateMem2 (d : PDesign) (args : List Int)
    (iterFuel : Nat := 4096) : Res MemDesign2 :=
  Kernel.instantiateMem2 d args iterFuel

def PDesign.instantiateMemD2 (d : PDesign) (args : List Int) : MemDesign2 :=
  Kernel.instantiateMemD2 d args

end LeanModels.Sv
