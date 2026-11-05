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
    (_iterFuel : Nat := 4096) : Res MemDesign2 := do
  if args.length != d.params.length then
    .unsupported s!"parameter arity: got {args.length}, want {d.params.length}"
  let env ← d.paramEnv2 args
  if !d.generates.isEmpty then
    .unsupported "memory cycle route does not yet admit generate members"
  if !d.others.isEmpty then
    .unsupported "memory cycle route does not yet admit unsupported module members"
  let decls ← scalarDeclsMem env d.decls
  let envP := { env with widths := decls.map fun dc => (dc.name, dc.width) }
  return { name := d.name, env := envP, decls, memDecls := memDeclsOf d,
           processes := d.processes }

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
      let value := dc.init.getD (LVec.xVec dc.width)
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

def evalMemExpr (d : MemDesign2) (fuel : Nat) (st : MemCycleState)
    (ctx : Option Nat) (e : PExpr) : Res LVec :=
  match e with
  | .arrayElem n is =>
      match memDeclOf? d.memDecls n with
      | none => .unsupported s!"memory RHS '{n}' is not declared"
      | some pd =>
          match MemState.readTarget d.env pd (.arrayElem n is) st.memory with
          | .error msg => .unsupported s!"memory RHS read: {msg}"
          | .ok none => .unsupported s!"memory RHS '{n}' is not a cell"
          | .ok (some v) => .ok v
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
          let v ← evalMemExpr d fuel st (pd.type.width d.env |>.toOption) e
          match MemState.writeTarget d.env pd lhs v st.memory with
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
          let rhs ← if memExprReadsArray e then
              match e with
              | .arrayElem rn ris => .ok (.cell pd (.arrayElem rn ris))
              | _ => .unsupported "memory NBA RHS is not a direct cell read"
            else .ok (.scalar (instExpr2 d.env [] (pd.type.width d.env |>.toOption) e))
          let q' ← execMemNba d.env fuel { scalar := st.scalar, memory := st.memory }
            q.2 pd lhs rhs
          return (st, (q.1, q'))
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
  | .alwaysComb _ => .unsupported "AlwaysComb:memory cycle route"
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

def memResetFires (prev cur : SvState) (rstn : String) : Bool :=
  isNegedge (SvState.bit0 prev rstn) (SvState.bit0 cur rstn)

def memStep (d : MemDesign2) (fuel : Nat) (inputs : SvState)
    (prev : MemCycleState) : Res MemCycleState := do
  let st0 := d.applyInputs inputs prev
  let q0 : MemPending := ([], [])
  let (st1, q1) ← if d.processes.any (fun p =>
      match p with | .alwaysFFR _ rst _ _ => memResetFires prev.scalar st0.scalar rst | _ => false) then
      d.processes.foldlM (init := (st0, q0)) fun acc p =>
        match p with
        | .alwaysFFR _ rst _ _ =>
            if memResetFires prev.scalar st0.scalar rst then runMemProcess d fuel acc.1 acc.2 p else .ok acc
        | _ => .ok acc
    else .ok (st0, q0)
  let st1 ← commitMemPending d st1 q1
  let (st2, q2) ← d.processes.foldlM (init := (st1, ([], []))) fun acc p =>
    match p with
    | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ _ =>
        runMemProcess d fuel acc.1 acc.2 p
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
