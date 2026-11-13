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
clock edges, continuous scalar assignments, one-shot time-zero initialization,
and a retained plain `always @*` body with raw-read sensitivity.  It does not
lower a loop to a block, expand a memory into cells, or introduce another
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
  | initial (body : PStmt)
  /-- A plain `always @*` waits for a raw read change before activation.
      Its source body remains a `PStmt`; the memory route does not lower it
      into a clocked or combinational surrogate. -/
  | implicit (body : PStmt)
  | unsupported (kind text : String)
deriving Repr, Inhabited

structure CoreMemDesign where
  name : String
  env : IEnv
  elems : List (String × Nat)
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

def CoreMemDesign.hasImplicit (E : CoreMemDesign) : Bool :=
  E.processes.toList.any fun p =>
    match p with
    | .implicit _ => true
    | _ => false

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
  | .alwaysImplicit body => .implicit body
  | .initial body => .initial body
  | .unsupported kind text => .unsupported kind text

/-! Module-level metadata that is already represented by retained source nodes.
An empty input-only task has no runtime effect, and the two x/z markers carry
the literal as a source `PExpr.lit`; admitting these markers therefore does not
invent a process or a value.  A scalar undriven four-state wire is admitted
only from the structured Slang metadata: IEEE 1800-2023 §6.6 gives it a z
startup value, while the absence of driver records means no resolution rule is
being inferred.  Other net shapes remain loud. -/

def coreMemAllowedOther (entry : String × String) : Bool :=
  entry.1 == "SubroutineSymbol:empty-task" ||
    entry.1 == "IntegerLiteral:unsized-xz-parametric" ||
    entry.1 == "ConversionExpression:xz-literal-parametric"

def coreMemNetMetadataAllowed (md : PNetMetadata) : Bool :=
  md.netKind == "Wire" && md.isNet && md.fourState && !md.signed &&
    md.driverReason == some "no driver: the net reads z" && md.driverRecords.isEmpty && md.width == 1

def coreMemNetAllowed (d : PDesign) (name : String) : Bool :=
  d.netMetadata.any fun md => md.name == name && coreMemNetMetadataAllowed md

def coreMemFirstUnsupportedOther (d : PDesign) : List (String × String) → Option (String × String)
  | [] => none
  | entry :: rest =>
      if coreMemAllowedOther entry ||
          (entry.1 == "NetSymbol:net-z" && coreMemNetAllowed d entry.2) then
        coreMemFirstUnsupportedOther d rest
      else some entry

def coreMemNetDecls (d : PDesign) : List Decl :=
  d.netMetadata.filterMap fun md =>
    if coreMemNetMetadataAllowed md then
      let dc : Decl := { name := md.name, width := md.width, init := some (LVec.replicate md.width .lz), isNet := true }
      some dc
    else none

def coreMemMetadataType (md : PNetMetadata) : PType :=
  if md.width == 1 then .packed [] (some 1)
  else .packed [⟨.int (Int.ofNat md.width - 1), .int 0⟩] (some md.width)

def coreMemMetadataDecl (md : PNetMetadata) : PDecl :=
  { name := md.name, type := coreMemMetadataType md, isSigned := md.signed,
    twoState := !md.fourState, isNet := md.isNet }

def coreMemMetadataDecls : List PNetMetadata → List PDecl
  | [] => []
  | md :: rest => coreMemMetadataDecl md :: coreMemMetadataDecls rest

/-! ## Source-shaped generate expansion

Generate elaboration selects and repeats the parser's process nodes; it does
not lower their bodies into `Process2` or expand memory declarations into
cells. A concrete genvar is retained as an integer expression in the copied
source node, so the canonical executor still sees the original `PProcess` /
`PStmt` shape and the native `MemState` route.
-/

def coreMemSubstExpr (vals : List (String × Int)) : PExpr → PExpr
  | .genvarRef n =>
      match vals.lookup n with
      | some v => .int v
      | none => .genvarRef n
  | .unary op a => .unary op (coreMemSubstExpr vals a)
  | .binary op a b => .binary op (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | .ternary c a b => .ternary (coreMemSubstExpr vals c) (coreMemSubstExpr vals a)
      (coreMemSubstExpr vals b)
  | .concat xs => .concat (xs.map (coreMemSubstExpr vals))
  | .resize w a => .resize w (coreMemSubstExpr vals a)
  | .signedResize w a => .signedResize w (coreMemSubstExpr vals a)
  | .squash2 w a => .squash2 w (coreMemSubstExpr vals a)
  | .sysCall fn a => .sysCall fn (coreMemSubstExpr vals a)
  | .bitSel a b => .bitSel (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | .partSel a b c => .partSel (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
      (coreMemSubstExpr vals c)
  | .repl a b => .repl (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | .reduce op a => .reduce op (coreMemSubstExpr vals a)
  | .cast s a => .cast s (coreMemSubstExpr vals a)
  | .arrayElem n xs => .arrayElem n (xs.map (coreMemSubstExpr vals))
  | .arrayPart n xs mode a b => .arrayPart n (xs.map (coreMemSubstExpr vals)) mode
      (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | .functionCall n xs => .functionCall n (xs.map (coreMemSubstExpr vals))
  | e => e

def coreMemSubstLhs (vals : List (String × Int)) : PLhs → PLhs
  | .bitSel n i => .bitSel n (coreMemSubstExpr vals i)
  | .partSel n a b => .partSel n (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | .concat xs => .concat (xs.map (coreMemSubstLhs vals))
  | .arrayElem n xs => .arrayElem n (xs.map (coreMemSubstExpr vals))
  | .arrayPart n xs mode a b => .arrayPart n (xs.map (coreMemSubstExpr vals)) mode
      (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | l => l

mutual
def coreMemSubstStmt (vals : List (String × Int)) : PStmt → PStmt
  | .blockingAssign n e => .blockingAssign n (coreMemSubstExpr vals e)
  | .nbaAssign n e => .nbaAssign n (coreMemSubstExpr vals e)
  | .ifStmt c t e => .ifStmt (coreMemSubstExpr vals c) (coreMemSubstStmt vals t)
      (coreMemSubstStmtOpt vals e)
  | .block xs => .block (coreMemSubstStmtList vals xs)
  | .forLoop n i c s b => .forLoop n (coreMemSubstExpr vals i)
      (coreMemSubstExpr vals c) (coreMemSubstExpr vals s) (coreMemSubstStmt vals b)
  | .blockingAssignL l e => .blockingAssignL (coreMemSubstLhs vals l)
      (coreMemSubstExpr vals e)
  | .nbaAssignL l e => .nbaAssignL (coreMemSubstLhs vals l)
      (coreMemSubstExpr vals e)
  | .caseStmt s items d mode check =>
      .caseStmt (coreMemSubstExpr vals s)
        (coreMemSubstCaseItems vals items) (coreMemSubstStmtOpt vals d) mode check
  | s => s
termination_by structural s => s

def coreMemSubstStmtOpt (vals : List (String × Int)) : Option PStmt → Option PStmt
  | none => none
  | some s => some (coreMemSubstStmt vals s)
termination_by structural o => o

def coreMemSubstStmtList (vals : List (String × Int)) : List PStmt → List PStmt
  | [] => []
  | s :: ss => coreMemSubstStmt vals s :: coreMemSubstStmtList vals ss
termination_by structural xs => xs

def coreMemSubstCaseItems (vals : List (String × Int)) :
    List (List PExpr × PStmt) → List (List PExpr × PStmt)
  | [] => []
  | (ps, b) :: rest =>
      (ps.map (coreMemSubstExpr vals), coreMemSubstStmt vals b) ::
        coreMemSubstCaseItems vals rest
termination_by structural xs => xs

def coreMemSubstProcess (vals : List (String × Int)) : PProcess → PProcess
  | .alwaysFF c b => .alwaysFF c (coreMemSubstStmt vals b)
  | .alwaysPlain c b => .alwaysPlain c (coreMemSubstStmt vals b)
  | .alwaysComb b => .alwaysComb (coreMemSubstStmt vals b)
  | .alwaysImplicit b => .alwaysImplicit (coreMemSubstStmt vals b)
  | .assign n e => .assign n (coreMemSubstExpr vals e)
  | .assignL l e => .assignL (coreMemSubstLhs vals l) (coreMemSubstExpr vals e)
  | .alwaysFFR c r b h => .alwaysFFR c r (coreMemSubstStmt vals b) h
  | .initial b => .initial (coreMemSubstStmt vals b)
  | p => p
end

def coreMemBindVals (env : IEnv) (vals : List (String × Int)) : IEnv :=
  -- `vals` is ordered from the innermost generate scope outward. Binding the
  -- reverse list preserves the head-first shadowing used by `lookup`.
  vals.reverse.foldl (fun e (n, v) => e.bindVal n v) env

mutual
def coreMemExpandItem (env : IEnv) (iterFuel : Nat) (vals : List (String × Int)) :
    GenItem → Res (List PProcess)
  | .process p => .ok [coreMemSubstProcess vals p]
  | .unsupported k t => .ok [.unsupported k t]
  | .inst i => .ok [.unsupported "Instance"
      s!"module instance '{i.name}' of '{i.module}' outside the canonical E memory route"]
  | .genIf cond thenB elseB =>
      match evalGenGuard (coreMemBindVals env vals) cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v => if v != 0 then coreMemExpandList env iterFuel vals thenB
                 else coreMemExpandList env iterFuel vals elseB
  | .genFor _label g initE bound step _rc body =>
      let env' := coreMemBindVals env vals
      match evalInt env' initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env' g bound δ iterFuel i0
          coreMemExpandIters env iterFuel vals g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

def coreMemExpandList (env : IEnv) (iterFuel : Nat) (vals : List (String × Int)) :
    List GenItem → Res (List PProcess)
  | [] => .ok []
  | it :: rest => do
      let ps ← coreMemExpandItem env iterFuel vals it
      let qs ← coreMemExpandList env iterFuel vals rest
      .ok (ps ++ qs)
  termination_by xs => (sizeOf xs, 0)
  decreasing_by all_goals (simp_wf; omega)

def coreMemExpandIters (env : IEnv) (iterFuel : Nat) (vals : List (String × Int))
    (g : String) : List Int → List GenItem → Res (List PProcess)
  | [], _ => .ok []
  | v :: vs, body => do
      let ps ← coreMemExpandList env iterFuel ((g, v) :: vals) body
      let qs ← coreMemExpandIters env iterFuel vals g vs body
      .ok (ps ++ qs)
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

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
    let generated ← coreMemExpandList env2 iterFuel [] d.generates
    match coreMemFirstUnsupportedOther d d.others with
    | some (kind, text) =>
      .unsupported s!"E memory route does not yet admit module member '{kind}' ({text})"
    | none =>
      let sourceDecls := d.decls ++ coreMemMetadataDecls d.netMetadata
      let decls0 ← buildScalarDecls1 env2 d.decls
      let decls := decls0 ++ coreMemNetDecls d
      let elems ← buildElems env2 sourceDecls
      let envP := { env2 with widths := decls.map (fun dc => (dc.name, dc.width)) }
      let memories ← buildMemDecls1 envP d.decls 0
      if memories.isEmpty && d.decls.any (fun pd => !pd.unpackedDims.isEmpty) then
        .unsupported "UnpackedDecl:memory: no one-rank unpacked declaration was admitted"
      else
        let scalar : Elab :=
          { name := d.name, decls := decls.toArray, procs := #[] }
        let scalarEdge : Elab1 :=
          { decls := decls.toArray, procs := #[], name := d.name }
        let processes := (d.processes.map CoreMemProc.ofPProcess) ++
          (generated.map CoreMemProc.ofPProcess)
        let result : CoreMemDesign :=
          { name := d.name, env := envP, elems, scalar := scalar, scalarEdge := scalarEdge,
            memories := memories.toArray, processes := processes.toArray }
        .ok result

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

/-! ## Raw sensitivity for retained implicit processes

Plain `always @*` is sensitive to every value read by its body (§9.4.2.2.2),
including the selected cell and index of a source-shaped memory read.  These
walkers retain the parser expressions; they do not lower a body or collapse a
memory into scalar cells. -/

mutual

def coreMemReadExprs : PExpr → List PExpr
  | e@(.ident _) => [e]
  | e@(.arrayElem _ indices) => e :: coreMemReadExprsList indices
  | e@(.arrayPart _ indices _ a b) =>
      e :: (coreMemReadExprsList indices ++ coreMemReadExprs a ++ coreMemReadExprs b)
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => coreMemReadExprs a
  | .binary _ a b | .bitSel a b | .repl a b =>
      coreMemReadExprs a ++ coreMemReadExprs b
  | .partSel a b c | .ternary a b c =>
      coreMemReadExprs a ++ coreMemReadExprs b ++ coreMemReadExprs c
  | .concat xs | .functionCall _ xs => coreMemReadExprsList xs
  | .lit _ | .fill _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .unsupported .. => []

def coreMemReadExprsList : List PExpr → List PExpr
  | [] => []
  | e :: rest => coreMemReadExprs e ++ coreMemReadExprsList rest

def coreMemLhsReadExprs : PLhs → List PExpr
  | .ident _ => []
  | .bitSel _ i => coreMemReadExprs i
  | .partSel _ a b => coreMemReadExprs a ++ coreMemReadExprs b
  | .concat xs => coreMemLhsReadExprsList xs
  | .arrayElem _ indices => coreMemReadExprsList indices
  | .arrayPart _ indices _ a b =>
      coreMemReadExprsList indices ++ coreMemReadExprs a ++ coreMemReadExprs b

def coreMemLhsReadExprsList : List PLhs → List PExpr
  | [] => []
  | lhs :: rest => coreMemLhsReadExprs lhs ++ coreMemLhsReadExprsList rest

def coreMemStmtReadExprs : PStmt → List PExpr
  | .blockingAssign _ value | .nbaAssign _ value => coreMemReadExprs value
  | .blockingAssignL target value | .nbaAssignL target value =>
      coreMemLhsReadExprs target ++ coreMemReadExprs value
  | .ifStmt cond yes no =>
      coreMemReadExprs cond ++ coreMemStmtReadExprs yes ++ coreMemStmtReadExprsOpt no
  | .block body => coreMemStmtReadExprsList body
  | .forLoop _ init condition step body =>
      coreMemReadExprs init ++ coreMemReadExprs condition ++ coreMemReadExprs step ++
        coreMemStmtReadExprs body
  | .caseStmt subject items default? _ _ =>
      coreMemReadExprs subject ++ coreMemCaseReadExprs items ++
        coreMemStmtReadExprsOpt default?
  | .unsupported .. => []

def coreMemStmtReadExprsOpt : Option PStmt → List PExpr
  | none => []
  | some body => coreMemStmtReadExprs body

def coreMemStmtReadExprsList : List PStmt → List PExpr
  | [] => []
  | stmt :: rest => coreMemStmtReadExprs stmt ++ coreMemStmtReadExprsList rest

def coreMemCaseReadExprs : List (List PExpr × PStmt) → List PExpr
  | [] => []
  | (patterns, body) :: rest =>
      coreMemReadExprsList patterns ++ coreMemStmtReadExprs body ++
        coreMemCaseReadExprs rest

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

/-! ## Time-zero source statements

An `initial` block is a time-zero process (§4.7), not a cycle edge.  The first
memory wall needs only the source-shaped initialization form used by real
register files: conditional/blocking statements and a run-time `for` whose
body writes one memory cell.  It updates the existing `MemState` directly;
it does not expand cells or turn the initializer into an edge process. -/

mutual

def CoreMemDesign.writeInitialCell (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState)
    (target : PLhs) (name : String) (md : CoreMemDecl) (value : LVec) : Res CoreMemState :=
  match LeanModels.Sv.MemState.writeTarget env md.source target value st.memory with
  | Except.ok (some memory) => .ok { scalar := st.scalar, memory := memory }
  | Except.ok none => .unsupported
      s!"11.5.1: memory initial target '{name}' is not one-rank"
  | Except.error msg => .unsupported msg

def CoreMemDesign.execInitialStmt (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) : PStmt → Res CoreMemState
  | .blockingAssign name value =>
      match E.scalarTarget name with
      | none => .unsupported s!"11.5.1: scalar initial target '{name}' is undeclared"
      | some width => do
          let v ← E.evalExpr env elems st (some width) value
          .ok { st with scalar := E.scalar.setName st.scalar name v }
  | .blockingAssignL target value =>
      match target with
      | .ident name =>
          match E.scalarTarget name with
          | none => .unsupported s!"11.5.1: scalar initial target '{name}' is undeclared"
          | some width => do
              let v ← E.evalExpr env elems st (some width) value
              .ok { st with scalar := E.scalar.setName st.scalar name v }
      | .arrayElem name [_] =>
          match E.memDecl? name with
          | none => .unsupported s!"11.5.1: memory initial target '{name}' is undeclared"
          | some md => do
              let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
              E.writeInitialCell env elems st target name md v
      | .arrayElem name _ =>
          .unsupported s!"11.5.1: memory initial target '{name}' is not one-rank"
      | _ => .unsupported "11.5.1: packed or concatenated initial target is outside this E slice"
  | .ifStmt cond yes no => do
      let cv ← E.evalExpr env elems st (some 1) cond
      if cv.condTrue then E.execInitialStmt env elems st yes
      else match no with
        | none => .ok st
        | some stmt => E.execInitialStmt env elems st stmt
  | .block body => E.execInitialStmts env elems st body
  | .forLoop iterator init condition step body =>
      match forValues2 env iterator init condition step with
      | .timeout => .timeout
      | .unsupported e => .unsupported s!"ForLoopStatement: {e}"
      | .ok values => E.execInitialLoop env elems st values body iterator
  | .nbaAssign .. | .nbaAssignL .. =>
      .unsupported "10.4.2: nonblocking assignment in a time-zero initializer"
  | .caseStmt .. => .unsupported "12.5: case in a time-zero initializer is outside this slice"
  | .unsupported kind text => .unsupported s!"{kind}: {text}"

def CoreMemDesign.execInitialStmts (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) : List PStmt → Res CoreMemState
  | [] => .ok st
  | stmt :: rest => do
      let st' ← E.execInitialStmt env elems st stmt
      E.execInitialStmts env elems st' rest

def CoreMemDesign.execInitialLoop (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) : List Int → PStmt → String → Res CoreMemState
  | [], _, _ => .ok st
  | i :: rest, body, iterator => do
      let st' ← E.execInitialStmt (env.bindVal iterator i) elems st body
      E.execInitialLoop env elems st' rest body iterator

end

def CoreMemDesign.initialState (E : CoreMemDesign) : Res CoreMemState :=
  let bodies := E.processes.toList.filterMap fun p =>
    match p with
    | .initial body => some body
    | _ => none
  match bodies with
  | [] => .ok E.initial
  | [body] => E.execInitialStmt E.env E.elems E.initial body
  | _ => .unsupported "T2:Initial: multiple initial processes are outside this cycle entry"

/-! ## Plain `always @*` activations

The process starts waiting (§9.4.2.2.2).  At a slot boundary its raw reads are
compared with the state before the slot, then the retained blocking body runs
once in source order.  A body that changes one of its own watched reads would
need a second Active-region pass; that cyclic shape stays loud instead of
being silently evaluated with a stale value. -/

def CoreMemDesign.readChanged (E : CoreMemDesign) (before after : CoreMemState)
    (reads : List PExpr) : Res Bool :=
  match reads with
  | [] => .ok false
  | expr :: rest => do
      let old ← E.evalExpr E.env E.elems before none expr
      let now ← E.evalExpr E.env E.elems after none expr
      if old == now then E.readChanged before after rest else .ok true

mutual

def CoreMemDesign.execImplicitStmt (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) : PStmt → Res CoreMemState
  | .blockingAssign name value =>
      match E.scalarTarget name with
      | none => .unsupported s!"9.2.2.2: scalar implicit target '{name}' is undeclared"
      | some width => do
          let v ← E.evalExpr env elems st (some width) value
          .ok { st with scalar := E.scalar.setName st.scalar name v }
  | .blockingAssignL target value =>
      match target with
      | .ident name =>
          match E.scalarTarget name with
          | none => .unsupported s!"9.2.2.2: scalar implicit target '{name}' is undeclared"
          | some width => do
              let v ← E.evalExpr env elems st (some width) value
              .ok { st with scalar := E.scalar.setName st.scalar name v }
      | .arrayElem name [_] =>
          match E.memDecl? name with
          | none => .unsupported s!"9.2.2.2: memory implicit target '{name}' is undeclared"
          | some md => do
              let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
              E.writeInitialCell env elems st target name md v
      | .arrayElem name _ =>
          .unsupported s!"9.2.2.2: memory implicit target '{name}' is not one-rank"
      | _ => .unsupported "9.2.2.2: packed or concatenated implicit target is outside this slice"
  | .ifStmt cond yes no => do
      let cv ← E.evalExpr env elems st (some 1) cond
      if cv.condTrue then E.execImplicitStmt env elems st yes
      else match no with
        | none => .ok st
        | some stmt => E.execImplicitStmt env elems st stmt
  | .block body => E.execImplicitStmts env elems st body
  | .forLoop .. =>
      .unsupported "9.2.2.2: procedural loop in implicit memory body is outside this slice"
  | .caseStmt .. =>
      .unsupported "12.5: case in implicit memory body is outside this slice"
  | .nbaAssign .. | .nbaAssignL .. =>
      .unsupported "10.4.2: nonblocking assignment in implicit memory body"
  | .unsupported kind text => .unsupported s!"{kind}: {text}"

def CoreMemDesign.execImplicitStmts (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) : List PStmt → Res CoreMemState
  | [] => .ok st
  | stmt :: rest => do
      let st' ← E.execImplicitStmt env elems st stmt
      E.execImplicitStmts env elems st' rest

end

def CoreMemDesign.runImplicit (E : CoreMemDesign) (before current : CoreMemState) :
    List CoreMemProc → Res CoreMemState
  | [] => .ok current
  | .implicit body :: rest => do
      let reads := coreMemStmtReadExprs body
      let ready ← E.readChanged before current reads
      if !ready then
        E.runImplicit before current rest
      else
        let after ← E.execImplicitStmt E.env E.elems current body
        let rearmed ← E.readChanged current after reads
        if rearmed then
          .unsupported
            "ProceduralBlockSymbol:Always: implicit event process re-triggered in one active pass"
        else
          E.runImplicit before after rest
  | .assign _ _ :: rest => E.runImplicit before current rest
  | .edge _ :: rest => E.runImplicit before current rest
  | .initial _ :: rest => E.runImplicit before current rest
  | .unsupported kind text :: _ => .unsupported s!"{kind}: {text}"

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
  | .initial _ :: rest => E.settleAssign env elems st rest
  | .implicit _ :: rest => E.settleAssign env elems st rest
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
  | .initial _ :: rest => E.runEdges env elems st before after rest
  | .implicit _ :: rest => E.runEdges env elems st before after rest
  | _ :: rest => E.runEdges env elems st before after rest

def CoreMemDesign.applyMemoryInputs (E : CoreMemDesign) (entry : SvState)
    (memory : MemState) : MemState :=
  E.memories.toList.foldl (fun mem md =>
    if !md.source.isInput then mem else
      let count := (Int.natAbs (md.shape.msb - md.shape.lsb)) + 1
      (List.range count).foldl (fun m k =>
        let ki : Int := Int.ofNat k
        let i := if md.shape.lsb >= md.shape.msb then md.shape.msb + ki else md.shape.msb - ki
        match SvState.lookup entry (md.source.name ++ "[" ++ toString i ++ "]") with
        | none => m
        | some v => (m.writeId md.shape.id i (md.shape.convert v)).getD m) mem) memory

def CoreMemDesign.step (E : CoreMemDesign) (st : CoreMemState) (entry : SvState) : Res CoreMemState := do
  let input := E.scalar.applyInputs st.scalar entry
  let memoryInput := E.applyMemoryInputs entry st.memory
  let pre ← E.settleAssign E.env E.elems { scalar := input, memory := memoryInput } E.processes.toList
  let before := E.scalar.view st.scalar
  let after := E.scalar.view pre.scalar
  let (scalarQ, memoryQ) ← E.runEdges E.env E.elems pre before after E.processes.toList
  let scalar := E.scalarEdge.commit pre.scalar scalarQ
  let memory ← match pre.memory.commitNba memoryQ with
    | some m => .ok m
    | none => .unsupported "10.4.2: memory NBA commit lost its declaration identity"
  let settled ← E.settleAssign E.env E.elems { scalar, memory } E.processes.toList
  let activated ← if E.hasImplicit then
      E.runImplicit st settled E.processes.toList
    else .ok settled
  E.settleAssign E.env E.elems activated E.processes.toList

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
