import LeanModels.Sv.Kernel.Core1Elab
import LeanModels.Sv.Kernel.MemElab
import LeanModels.Sv.Loop2

/-!
# Source-shaped one-rank memories in canonical E

This is the first memory extension of E-core-1.  The scalar part is the
canonical `Store`/`Elab1` store and its scalar NBA queue; unpacked storage is
one native `MemState`.  The source `PStmt` is retained, including a procedural
`forLoop`, and the loop is evaluated from `Loop2.headerSchema` at run time.

The adapter is deliberately small: one-rank unpacked declarations, positive
clock edges, continuous scalar assignments, and NBA-only edge bodies.  It does
not lower a loop to a block, expand a memory into cells, or introduce another
memory representation.  Unknown and out-of-range memory indices use
`MemState.issueNba`/`readIndexId`, so issue-time NBA sampling and x/no-op
behavior are shared with the canonical memory component.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Source-shaped elaboration -/

structure CoreMemDecl where
  source : PDecl
  shape : MemShape
deriving Repr, Inhabited

structure CoreMemEdge where
  clock : String
  reset : Option String := none
  body : PStmt
  style : EdgeStyle := .alwaysFF
deriving Repr, Inhabited

inductive CoreMemProc where
  | edge (p : CoreMemEdge)
  | assign (target : PLhs) (value : PExpr)
  | unsupported (kind text : String)
deriving Repr, Inhabited

structure CoreMemDesign where
  name : String
  env : IEnv
  scalar : Elab
  scalarEdge : Elab1
  memories : Array CoreMemDecl
  processes : Array CoreMemProc

structure CoreMemState where
  scalar : Store
  memory : MemState

def CoreMemDesign.initial (E : CoreMemDesign) : CoreMemState :=
  { scalar := E.scalar.initStore
    memory := MemState.ofShapes (E.memories.toList.map CoreMemDecl.shape) }

def CoreMemDesign.memDecl? (E : CoreMemDesign) (name : String) : Option CoreMemDecl :=
  E.memories.toList.find? (fun d => d.source.name == name)

def CoreMemDesign.scalarWidth? (E : CoreMemDesign) (name : String) : Option Nat :=
  match E.scalar.resolve name with
  | some x => (E.scalar.declOf x).map Decl.width
  | none => none

def CoreMemDesign.scalarE (E : CoreMemDesign) : Elab1 := E.scalarEdge

def instScalarDecl1 (env : IEnv) (pd : PDecl) : Res (Option Decl) :=
  if !pd.unpackedDims.isEmpty then
    .ok none
  else
    match pd.type.width env with
    | .error e => .unsupported s!"decl '{pd.name}': {e}"
    | .ok w =>
        match pd.init with
        | none =>
            let dc : Decl :=
              { name := pd.name, width := w, isSigned := pd.isSigned,
                isNet := pd.isNet, twoState := pd.twoState,
                isInput := pd.isInput, isOutput := pd.isOutput }
            .ok (some dc)
        | some init =>
            match instExpr env (some w) init with
            | .lit v =>
                let dc : Decl :=
                  { name := pd.name, width := w, isSigned := pd.isSigned,
                    isNet := pd.isNet, twoState := pd.twoState,
                    isInput := pd.isInput, isOutput := pd.isOutput, init := some v }
                .ok (some dc)
            | _ => .unsupported s!"decl '{pd.name}': non-literal initializer outside E"

def buildScalarDecls1 (env : IEnv) : List PDecl → Res (List Decl)
  | [] => .ok []
  | pd :: rest => do
      let dc? ← instScalarDecl1 env pd
      let rest' ← buildScalarDecls1
        (match dc? with
         | some dc => { env with widths := (pd.name, dc.width) :: env.widths }
         | none => env) rest
      match dc? with
      | some dc => .ok (dc :: rest')
      | none => .ok rest'

def buildMemDecls1 (env : IEnv) : List PDecl → Nat → Res (List CoreMemDecl)
  | [], _ => .ok []
  | pd :: rest, ordinal => do
      let tail ← buildMemDecls1 env rest (ordinal + 1)
      match pd.memShapeWithId? env ({ decl := ordinal } : MemId) with
      | .error e => .unsupported e
      | .ok none => .ok tail
      | .ok (some shape) => .ok ({ source := pd, shape } :: tail)

def CoreMemProc.ofPProcess : PProcess → CoreMemProc
  | .alwaysFF clock body => .edge { clock, body, style := .alwaysFF }
  | .alwaysPlain clock body => .edge { clock, body, style := .alwaysPlain }
  | .alwaysFFR clock reset body high =>
      if high then .unsupported "9.4.2" "active-high asynchronous reset is outside canonical E"
      else .edge { clock, reset := some reset, body, style := .alwaysFF }
  | .assign target value => .assign (.ident target) value
  | .assignL target value => .assign target value
  | .alwaysComb _ => .unsupported "9.2.2.2" "always_comb is outside this memory edge slice"
  | .alwaysImplicit _ => .unsupported "ProceduralBlockSymbol:Always"
      "implicit event control is outside the canonical memory edge slice"
  | .initial _ => .unsupported "T2:Initial" "initial process is outside this cycle entry"
  | .unsupported kind text => .unsupported kind text

def PDesign.instantiateCoreMemFrom (envI : IEnv) (d : PDesign) (args : List Int)
    (iterFuel : Nat := 4096) : Res CoreMemDesign := do
  if args.length != d.params.length then
    .unsupported s!"parameter arity: got {args.length}, want {d.params.length}"
  else
    let envP ← bindPackageParams envI d.packageParams
    let envP ← bindPackageEnums envP d.enums
    let env0 ← bindParamsRes envP d.params args
    let env1 ← bindLocals env0 d.localParams
    let env2 ← bindEnums env1 d.enums
    let pws ← typedParamWidthsE env2
      (d.params.map (fun p => (p.name, p.type?))
        ++ d.localParams.map (fun lp => (lp.name, lp.type?)))
    let env2 := { env2 with pwidths := pws }
    let env2 := { env2 with dims := dimTable env2 d.decls }
    let env2 := { env2 with functions := d.functions }
    if !d.generates.isEmpty then
      .unsupported "E memory route does not yet admit generate items"
    else if !d.others.isEmpty then
      .unsupported "E memory route does not yet admit hierarchy items"
    else
      let decls ← buildScalarDecls1 env2 d.decls
      let elems ← buildElems env2 d.decls
      let envP := { env2 with widths := decls.map (fun dc => (dc.name, dc.width)) }
      let memories ← buildMemDecls1 envP d.decls 0
      if memories.isEmpty && d.decls.any (fun pd => !pd.unpackedDims.isEmpty) then
        .unsupported "UnpackedDecl:memory: no one-rank unpacked declaration was admitted"
      else
        let scalar : Elab :=
          { name := d.name, decls := decls.toArray, procs := #[] }
        let scalarEdge : Elab1 :=
          { decls := decls.toArray, procs := #[], name := d.name }
        .ok ({ name := d.name, env := envP, scalar := scalar, scalarEdge := scalarEdge, memories := memories.toArray, processes := (d.processes.map CoreMemProc.ofPProcess).toArray } : CoreMemDesign)

def PDesign.instantiateCoreMem (d : PDesign) (args : List Int)
    (iterFuel : Nat := 4096) : Res CoreMemDesign :=
  PDesign.instantiateCoreMemFrom { int32 := true } d args iterFuel

/-! ## Expressions -/

mutual

def LeanModels.Sv.PExpr.hasMemoryRead : PExpr → Bool
  | .arrayElem .. | .arrayPart .. => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => LeanModels.Sv.PExpr.hasMemoryRead a
  | .binary _ a b => LeanModels.Sv.PExpr.hasMemoryRead a || LeanModels.Sv.PExpr.hasMemoryRead b
  | .ternary c a b => LeanModels.Sv.PExpr.hasMemoryRead c ||
      LeanModels.Sv.PExpr.hasMemoryRead a || LeanModels.Sv.PExpr.hasMemoryRead b
  | .concat xs => PExpr.hasMemoryReadList xs
  | .functionCall _ xs => PExpr.hasMemoryReadList xs
  | .bitSel a b | .repl a b => LeanModels.Sv.PExpr.hasMemoryRead a ||
      LeanModels.Sv.PExpr.hasMemoryRead b
  | .partSel a b c => LeanModels.Sv.PExpr.hasMemoryRead a ||
      LeanModels.Sv.PExpr.hasMemoryRead b || LeanModels.Sv.PExpr.hasMemoryRead c
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .fill _ | .unsupported .. => false

def LeanModels.Sv.PExpr.hasMemoryReadList : List PExpr → Bool
  | [] => false
  | x :: xs => LeanModels.Sv.PExpr.hasMemoryRead x ||
      LeanModels.Sv.PExpr.hasMemoryReadList xs

end

def evalMemUnary (op : SymUnaryOp) (v : LVec) : Res LVec :=
  match op with
  | .m0 op => .ok (evalUnaryOp op v)
  | .plus => .ok (evalUnaryOp .pos v)
  | .inc | .dec => .unsupported
    "UnaryExpression:incdec: increment/decrement is only a procedural loop step"

def evalMemBin (op : SymBinOp) (a b : LVec) : Res LVec :=
  match op with
  | .m0 op => .ok (evalBinOp op a b)
  | .mul => .ok (evalBinOp .mul a b)
  | .div => .ok (evalBinOp .div a b)
  | .mod => .ok (evalBinOp .rem a b)
  | .pow => .ok (evalBinOp (.pow false false) a b)
  | .shl => .ok (evalBinOp (.shl false) a b)
  | .shr => .ok (evalBinOp (.shr false) a b)
  | .ashl => .ok (evalBinOp (.ashl false) a b)
  | .ashr => .ok (evalBinOp (.ashr false) a b)
  | .slt => .ok (evalBinOp .slt a b)
  | .sle => .ok (evalBinOp .sle a b)
  | .sgt => .ok (evalBinOp .sgt a b)
  | .sge => .ok (evalBinOp .sge a b)
  | .ceq => .ok (evalBinOp .caseEq a b)
  | .cne => .ok (evalBinOp .caseNe a b)
  | .land => .ok (evalBinOp .land a b)
  | .lor => .ok (evalBinOp .lor a b)

def CoreMemDesign.evalScalar (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (ctx : Option Nat) (e : PExpr) : Res LVec :=
  evalPure2 (E.scalar.view st.scalar) (instExpr2 env elems ctx e)

mutual

def CoreMemDesign.evalIndex (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (e : PExpr) : Res LVec :=
  match evalInt env e with
  | .ok i => .ok (LVec.ofInt 32 i)
  | .error _ => E.evalExpr env elems st none e

def CoreMemDesign.evalExpr (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (ctx : Option Nat) : PExpr → Res LVec
  | e@(.arrayElem name [index]) => do
      let some md := E.memDecl? name
        | .unsupported s!"ArraySel: memory declaration '{name}' is not present"
      let idx ← E.evalIndex env elems st index
      match st.memory.readIndexId md.shape.id false idx with
      | some v => .ok v
      | none => .unsupported s!"ArraySel: memory identity for '{name}' is not present"
  | .arrayElem name _ =>
      .unsupported s!"ArraySel:rank: memory '{name}' is not a one-rank element select"
  | .arrayPart name _ _ _ _ =>
      .unsupported s!"ArraySel:part: memory '{name}' part select is outside this E slice"
  | e@(.unary op a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        evalMemUnary op (← E.evalExpr env elems st ctx a)
      else E.evalScalar env elems st ctx e
  | e@(.binary op a b) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        evalMemBin op (← E.evalExpr env elems st ctx a) (← E.evalExpr env elems st ctx b)
      else E.evalScalar env elems st ctx e
  | e@(.ternary c a b) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then
        do
          let cv ← E.evalExpr env elems st none c
          let tv ← E.evalExpr env elems st ctx a
          let fv ← E.evalExpr env elems st ctx b
          .ok (LVec.ternary cv tv fv)
      else E.evalScalar env elems st ctx e
  | e@(.concat xs) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let vs ← evalMemExprList E env elems st xs
        .ok (LVec.concatMany vs.toArray)
      else E.evalScalar env elems st ctx e
  | e@(.resize _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let v ← E.evalExpr env elems st ctx a
        .ok (v.resizeU (ctx.getD v.width))
      else E.evalScalar env elems st ctx e
  | e@(.signedResize _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let v ← E.evalExpr env elems st ctx a
        .ok (v.resizeSigned (ctx.getD v.width))
      else E.evalScalar env elems st ctx e
  | e@(.squash2 _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        return (← E.evalExpr env elems st ctx a).toTwoState
      else E.evalScalar env elems st ctx e
  | e => E.evalScalar env elems st ctx e

def evalMemExprList (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) : List PExpr → Res (List LVec)
  | [] => .ok []
  | e :: es => do
      let v ← E.evalExpr env elems st none e
      let vs ← evalMemExprList E env elems st es
      .ok (v :: vs)

end

/-! ## Source-shaped edge bodies -/

abbrev CoreMemExec := Res (NbaQueue2 × MemNbaQueue)

def CoreMemDesign.scalarTarget (E : CoreMemDesign) (name : String) : Option Nat :=
  E.scalarWidth? name

def CoreMemDesign.issueTarget (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (target : PLhs) (value : LVec) : CoreMemExec :=
  match target with
  | .ident name =>
      match E.scalarTarget name with
      | some _ => .ok ([(name, 0, value)], [])
      | none => .unsupported s!"11.5.1: scalar NBA target '{name}' is undeclared"
  | .arrayElem name [index] =>
      match E.memDecl? name with
      | none => .unsupported s!"11.5.1: memory NBA target '{name}' is undeclared"
      | some md =>
          let idx := E.evalIndex env elems st index
          match idx with
          | .timeout => .timeout
          | .unsupported m => .unsupported m
          | .ok iv =>
              match st.memory.issueNba md.shape.id false iv value with
              | .missing => .unsupported s!"11.5.1: memory identity for '{name}' is not present"
              | .noOp => .ok ([], [])
              | .queued u => .ok ([], [u])
  | .arrayElem name _ =>
      .unsupported s!"11.5.1: memory NBA target '{name}' is not one-rank"
  | _ => .unsupported "11.5.1: packed or concatenated memory NBA target is outside this E slice"

def CoreMemExec.append (a b : NbaQueue2 × MemNbaQueue) : NbaQueue2 × MemNbaQueue :=
  (a.1 ++ b.1, a.2 ++ b.2)

mutual

def CoreMemDesign.execStmt (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) : PStmt → CoreMemExec
  | .nbaAssign target value =>
      match E.scalarTarget target with
      | none => .unsupported s!"11.5.1: scalar NBA target '{target}' is undeclared"
      | some width => do
          let v ← E.evalExpr env elems st (some width) value
          E.issueTarget env elems st (.ident target) v
  | .nbaAssignL target value =>
      match target with
      | .ident name =>
          match E.scalarTarget name with
          | none => .unsupported s!"11.5.1: scalar NBA target '{name}' is undeclared"
          | some width => do
              let v ← E.evalExpr env elems st (some width) value
              E.issueTarget env elems st target v
      | .arrayElem name [index] =>
          match E.memDecl? name with
          | none => .unsupported s!"11.5.1: memory NBA target '{name}' is undeclared"
          | some md => do
              let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
              E.issueTarget env elems st target v
      | _ => .unsupported "11.5.1: memory target is outside the one-rank element tier"
  | .blockingAssign _ _ | .blockingAssignL _ _ =>
      .unsupported "9.2.2.1: blocking assignment in a canonical E edge body"
  | .ifStmt cond yes no => do
      let cv ← E.evalExpr env elems st (some 1) cond
      if cv.condTrue then E.execStmt env elems st yes
      else match no with | none => .ok ([], []) | some s => E.execStmt env elems st s
  | .block body => E.execStmts env elems st body
  | .forLoop iterator init condition step body =>
      match forValues2 env iterator init condition step with
      | .timeout => .timeout
      | .unsupported e => .unsupported s!"ForLoopStatement: {e}"
      | .ok values => E.execLoopValues env elems st values body iterator
  | .caseStmt .. => .unsupported "12.5: case in a canonical memory loop body is outside this slice"
  | .unsupported kind text => .unsupported s!"{kind}: {text}"

def CoreMemDesign.execStmts (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) : List PStmt → CoreMemExec
  | [] => .ok ([], [])
  | stmt :: rest => do
      let a ← E.execStmt env elems st stmt
      let b ← E.execStmts env elems st rest
      .ok (CoreMemExec.append a b)

def CoreMemDesign.execLoopValues (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) : List Int → PStmt → String → CoreMemExec
  | [], _, _ => .ok ([], [])
  | i :: rest, body, iterator => do
      let a ← E.execStmt (env.bindVal iterator i) elems st body
      let b ← E.execLoopValues env elems st rest body iterator
      .ok (CoreMemExec.append a b)

end

/-! ## Slots, scalar E commit, and memory commit -/

def CoreMemEdge.fires (p : CoreMemEdge) (before after : SvState) : Bool :=
  isPosedge (before.bit0 p.clock) (after.bit0 p.clock) ||
    match p.reset with
    | none => false
    | some r => isNegedge (before.bit0 r) (after.bit0 r)

def CoreMemDesign.settleAssign (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) : List CoreMemProc → Res CoreMemState
  | [] => .ok st
  | .assign target value :: rest => do
      let width ← match E.scalarWidth? target.name with
        | some w => .ok w
        | none => .unsupported s!"10.3: continuous target '{target.name}' is undeclared"
      let v ← E.evalExpr env elems st (some width) value
      let scalar := E.scalar.setName st.scalar target.name v
      E.settleAssign env elems { st with scalar } rest
  | .edge _ :: rest => E.settleAssign env elems st rest
  | .unsupported kind text :: _ =>
      .unsupported s!"{kind}: {text}"

def CoreMemDesign.runEdges (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (before after : SvState) : List CoreMemProc → CoreMemExec
  | [] => .ok ([], [])
  | .edge p :: rest =>
      if p.fires before after then do
        let a ← E.execStmt env elems st p.body
        let b ← E.runEdges env elems st before after rest
        .ok (CoreMemExec.append a b)
      else E.runEdges env elems st before after rest
  | _ :: rest => E.runEdges env elems st before after rest

def CoreMemDesign.step (E : CoreMemDesign) (st : CoreMemState) (entry : SvState) : Res CoreMemState := do
  let input := E.scalar.applyInputs st.scalar entry
  let pre ← E.settleAssign E.env [] { scalar := input, memory := st.memory } E.processes.toList
  let before := E.scalar.view st.scalar
  let after := E.scalar.view pre.scalar
  let (scalarQ, memoryQ) ← E.runEdges E.env [] pre before after E.processes.toList
  let scalar := E.scalarEdge.commit pre.scalar scalarQ
  let memory ← match pre.memory.commitNba memoryQ with
    | some m => .ok m
    | none => .unsupported "10.4.2: memory NBA commit lost its declaration identity"
  E.settleAssign E.env [] { scalar, memory } E.processes.toList

def runCoreMemRows (E : CoreMemDesign) (st : CoreMemState) : List SvState → Res (List CoreMemState)
  | [] => .ok []
  | row :: rest => do
      let st' ← E.step st row
      let tail ← runCoreMemRows E st' rest
      .ok (st' :: tail)

def CoreMemState.view (E : CoreMemDesign) (st : CoreMemState) : SvState := E.scalar.view st.scalar

/-! ## Kernel smoke checks -/

private def smokeShape : MemShape :=
  { name := "s", elemWidth := 4, msb := 0, lsb := 2, id := { decl := 0 } }

private def smokeDecl : PDecl :=
  { name := "s", type := .packed [⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1), .int 0⟩] none,
    unpackedDims := [⟨.int 0, .binary (.m0 .sub) (.paramRef "P" none) (.int 1)⟩] }

#guard (smokeDecl.memShapeWithId? { vals := [("W", 4), ("P", 3)] } { decl := 0 }).toOption ==
  some smokeShape

end LeanModels.Sv.Kernel

#print axioms LeanModels.Sv.Kernel.CoreMemDesign.step
