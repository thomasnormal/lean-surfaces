import LeanModels.Sv.Kernel.MemElab
import LeanModels.Sv.Gen2
import LeanModels.Sv.Loop2
import LeanModels.Sv.PreemptGuard2

/-!
# The first source-shaped memory step in E

This is the small E memory profile used by a clean-room FIFO wall.  It keeps
unpacked declarations and `ArraySel` targets in the parser AST; there is no
cell expansion and no run2/MemCycle adapter.  The profile admits one-rank
memories, an active-low reset edge body made of `if`/`begin`/NBA statements,
and continuous scalar assignments whose right hand side is a direct memory
cell.  Other shapes return a named refusal.

The recursive definitions are over source lists/statements, so the semantic
meaning has no fuel.  A bounded executor may be added above this module later;
this file is the E-side state and one-cycle transition only.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv
open LeanModels.Sv.CombGuard

set_option autoImplicit false

structure MemEDesign where
  name : String
  env : IEnv
  decls : List Decl
  memDecls : List PDecl
  processes : List PProcess
  /-- Module-member markers retained by the symbolic frontend.  The E
      profile consumes only the explicitly admitted markers below; every
      other unsupported member remains a loud boundary. -/
  others : List (String × String) := []
  /-- Structured literal-file tasks retained by the parser frontend.  The
      E profile consumes these at time zero; it never recovers them from an
      Unsupported message. -/
  readmemh : List PReadmemh := []
  /-- Source declarations retained for fixed unpacked arrays whose cells are
      represented as scalar declarations by the frontend. -/
  sourceDecls : List PDecl := []
  /-- Hierarchical port connections settle once before an edge, as required
      by the active-region ordering of an instantiated child. -/
  preSettle : Bool := false
deriving Repr, Inhabited

structure MemEState where
  scalar : SvState
  memory : MemState
deriving Inhabited

inductive MemEUpdate where
  | scalar (name : String) (value : LVec)
  | cell (name : String) (index : Int) (value : LVec)
deriving Repr, Inhabited

def resToExcept {α : Type} : Res α → Except String α
  | .ok v => .ok v
  | .timeout => .error "E memory expression exhausted"
  | .unsupported msg => .error msg

/-! ## Retained module members

The symbolic extractor keeps module members outside the ordinary declaration
vocabulary as structured `(sv_kind, text)` markers in `PDesign.others`.  The
memory profile admits only the exact shapes modelled here: an undriven scalar
four-state wire and a referenced input-only task whose body is the empty
statement.  IEEE 1800-2023 §6.6 gives an undriven net the high-impedance value
`z`; the empty task has no effect when its parser-retained call is executed.
The parser has already identified each marker and supplied its source-shaped
metadata; this code does not recover or parse source text.  The two x/z literal
markers are metadata for retained expression nodes handled by `evalMemEExpr`
and therefore do not allocate a declaration here. -/

def memEAllowedOther (entry : String × String) : Bool :=
  entry.1 == "SubroutineSymbol:empty-task" ||
    entry.1 == "NetSymbol:net-z" ||
    entry.1 == "IntegerLiteral:unsized-xz-parametric" ||
    entry.1 == "ConversionExpression:xz-literal-parametric"

def memEOtherDecls : List (String × String) → List Decl
  | [] => []
  | (kind, name) :: rest =>
      (if kind == "NetSymbol:net-z" then
        [{ name := name, width := 1, isNet := true,
           init := some (LVec.replicate 1 .lz) }]
       else []) ++ memEOtherDecls rest

def MemEDesign.memDecl? (d : MemEDesign) (name : String) : Option PDecl :=
  d.memDecls.find? (fun p => p.name == name)

def MemEDesign.elemWidths (d : MemEDesign) : List (String × Nat) :=
  d.decls.map (fun dc => (dc.name, dc.width))

def MemEDesign.shape? (d : MemEDesign) (pd : PDecl) : Except String MemShape := do
  match ← pd.memShape? d.env with
  | some shape => .ok shape
  | none => .error s!"decl '{pd.name}' is not an unpacked memory"

def MemEDesign.init (d : MemEDesign) : MemEState :=
  { scalar := d.decls.map (fun dc =>
      let value := dc.init.getD (if dc.isNet then LVec.replicate dc.width .lz
        else LVec.xVec dc.width)
      (dc.name, if dc.twoState then value.toTwoState else value))
    memory := MemState.ofShapes (d.memDecls.filterMap fun pd =>
      match pd.memShape? d.env with
      | .ok (some shape) => some shape
      | _ => none) }

private def firstMemEOrderConflict : List ProcessAccess → Nat → Option (Nat × Nat)
  | [], _ => none
  | a :: rest, i =>
      match rest.findIdx? (fun b => CombGuard.touches a.1 b.2) with
      | some j => some (i, i + j + 1)
      | none => firstMemEOrderConflict rest (i + 1)

/-! The memory profile makes one source-order pass over continuous drivers.
    A driver that reads a signal written by a later driver would require a
    second settle pass (§10.3/§4.5); refuse that shape before returning a
    stale value. -/
def MemEDesign.memoryOrderReport (d : MemEDesign) : Option (String × String) :=
  let comb := d.processes.filter fun p =>
    match p with
    | .assign .. | .assignL .. | .alwaysComb .. => true
    | _ => false
  let elems := d.elemWidths
  let wd := fun n => d.env.widths.lookup n
  let accesses := comb.map fun p =>
    Process2.preemptAccess wd (instProcess2 d.env elems p)
  match firstMemEOrderConflict accesses 0 with
  | none => none
  | some (i, j) =>
      some ("Schedule:comb-source-order",
        s!"comb process {i} reads a signal written by later comb process {j}; the source-order memory pass would need a second settle pass under IEEE 1800-2023 §10.3/§4.5")

/-! ## Literal-file initialization -/

def memEReadmemhDigit (c : Char) : Option Nat :=
  if c >= '0' && c <= '9' then some (c.toNat - '0'.toNat)
  else if c >= 'a' && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
  else if c >= 'A' && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def memEReadmemhNat (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.toList.foldlM (init := 0) fun n c => do
    let digit ← memEReadmemhDigit c
    return n * 16 + digit

def MemEDesign.writeReadmemhMem (d : MemEDesign) (st : MemEState)
    (pd : PDecl) (shape : MemShape) (index step : Int)
    : List String → Except String MemEState
  | [] => .ok st
  | word :: rest => do
      let n ← match memEReadmemhNat word with
        | some n => .ok n
        | none => .error "SystemTask:readmemh:xz-digit"
      let value := LVec.ofNat shape.elemWidth n
      let target := PLhs.arrayElem pd.name [.int index]
      let memory ← match MemState.writeTarget d.env pd target value st.memory with
        | .ok (some m) => .ok m
        | .ok none => .error "SystemTask:readmemh target is outside the memory shape"
        | .error e => .error e
      writeReadmemhMem d { st with memory } pd shape (index + step) step rest

def MemEDesign.flatIndices (target : String) : List PDecl → Except String (List Int)
  | [] => .ok []
  | pd :: rest => do
      if pd.flatBase != some target then
        .error s!"SystemTask:readmemh target '{target}' has a non-contiguous flat declaration"
      let some index := pd.flatIndex
        | .error s!"SystemTask:readmemh cell '{pd.name}' has no source index"
      let tail ← MemEDesign.flatIndices target rest
      .ok (index :: tail)

def MemEDesign.flatOrderOk : List Int → Bool
  | [] | [_] => true
  | first :: second :: rest =>
      let step := second - first
      (step == 1 || step == -1) && go step second rest
where
  go (step previous : Int) : List Int → Bool
    | [] => true
    | index :: rest => index - previous == step && go step index rest

def MemEDesign.writeReadmemhFlat (d : MemEDesign) (st : MemEState)
    (target : String) : List PDecl → List String → Except String MemEState
  | [], [] => .ok st
  | pd :: cells, word :: words => do
      let n ← match memEReadmemhNat word with
        | some n => .ok n
        | none => .error "SystemTask:readmemh:xz-digit"
      let some dc := d.decls.find? (·.name == pd.name)
        | .error s!"SystemTask:readmemh cell '{pd.name}' is not declared"
      writeReadmemhFlat d
        { st with scalar := SvState.set st.scalar pd.name (LVec.ofNat dc.width n) }
        target cells words
  | _, _ =>
      .error s!"SystemTask:readmemh:short-file for target '{target}'"

def MemEDesign.writeReadmemh (d : MemEDesign) (st : MemEState)
    (task : PReadmemh) : Except String MemEState := do
  match d.memDecl? task.target with
  | some pd =>
      let shape ← d.shape? pd
      let count := (Int.natAbs (shape.msb - shape.lsb)) + 1
      if task.words.length != count then
        .error s!"SystemTask:readmemh:short-file: {task.words.length} words for {count} cells"
      let step : Int := if shape.lsb >= shape.msb then 1 else -1
      writeReadmemhMem d st pd shape shape.msb step task.words
  | none =>
      let cells := d.sourceDecls.filter (fun pd => pd.flatBase == some task.target)
      if cells.isEmpty then
        .error s!"SystemTask:readmemh target '{task.target}' is not a declared memory"
      else
        let indexes ← MemEDesign.flatIndices task.target cells
        if !MemEDesign.flatOrderOk indexes then
          .error s!"SystemTask:readmemh target '{task.target}' has non-contiguous source indices"
        else
          writeReadmemhFlat d st task.target cells task.words

def MemEDesign.writeReadmemhList (d : MemEDesign) (st : MemEState) :
    List PReadmemh → Except String MemEState
  | [] => .ok st
  | task :: rest => do
      let st' ← d.writeReadmemh st task
      d.writeReadmemhList st' rest

def MemEDesign.applyInputs (d : MemEDesign) (inputs : SvState) (s : MemEState) : MemEState :=
  let scalar := d.decls.foldl (fun st dc =>
      if dc.isInput then
        match SvState.lookup inputs dc.name with
        | some v => SvState.set st dc.name (if dc.twoState then v.toTwoState else v)
        | none => st
      else st) s.scalar
  let memory := d.memDecls.foldl (fun mem pd =>
    if !pd.isInput then mem else
      match pd.memShape? d.env with
      | .ok (some shape) =>
          let count := (Int.natAbs (shape.msb - shape.lsb)) + 1
          (List.range count |>.map Int.ofNat).foldl (fun m k =>
            let i := if shape.lsb >= shape.msb then shape.msb + k else shape.msb - k
            match SvState.lookup inputs (pd.name ++ "[" ++ toString i ++ "]") with
            | none => m
            | some v => (m.write pd.name i (if pd.twoState then v.toTwoState else v)).getD m) mem
      | _ => mem) s.memory
  { scalar, memory }

mutual

def memEReadsArray : PExpr → Bool
  | .arrayElem .. | .arrayPart .. => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => memEReadsArray a
  | .binary _ a b | .bitSel a b | .repl a b => memEReadsArray a || memEReadsArray b
  | .partSel a b c | .ternary a b c => memEReadsArray a || memEReadsArray b || memEReadsArray c
  | .concat xs => memEReadsArrayList xs
  | .functionCall .. => false
  | .lit _ | .fill _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .unsupported .. => false

def memEReadsArrayList : List PExpr → Bool
  | [] => false
  | x :: xs => memEReadsArray x || memEReadsArrayList xs

end

def evalMemEIndex (d : MemEDesign) (s : MemEState) (e : PExpr) : Except String (Option Int) := do
  match evalInt d.env e with
  | .ok i => .ok (some i)
  | .error _ =>
      let idx := instExpr2 d.env d.elemWidths (some 32) e
      match resToExcept (evalPure2 s.scalar idx) with
      | .error _ => .ok none
      | .ok v => .ok (indexInt? idx v)

/-- Evaluate the parser's point-dependent unsized x/z conversion marker.

The symbolic extractor keeps the literal's canonical 32-bit, MSB-first
payload in `ConversionExpression:unsized-xz`; the destination width is only
known after this E memory design has been instantiated.  Reuse the generic
`unsizedXZ2` rule here so the E route applies IEEE 1800-2023 §5.7.1 (low-bit
truncation and most-significant x/z extension) without lowering the source
node into a fill or an ordinary literal before the context is known.
-/
def evalMemEUnsizedXZ (ctx : Option Nat) (payload : String) : Except String LVec :=
  match unsizedXZ2 ctx payload with
  | .lit value => .ok value
  | .unsupported _ message => .error message
  | _ => .error "unsized x/z conversion did not produce a literal"

def evalMemEExpr (d : MemEDesign) (s : MemEState) (ctx : Option Nat) : PExpr → Except String LVec
  | .arrayElem n [idx] => do
      match d.memDecl? n with
      | none => .error s!"memory RHS '{n}' is not declared"
      | some pd =>
          let shape ← d.shape? pd
          let i? ← evalMemEIndex d s idx
          match i? with
          | none => .ok (LVec.xVec shape.elemWidth)
          | some i => .ok ((s.memory.read n i).getD (LVec.xVec shape.elemWidth))
  | .arrayElem n _ => .error s!"memory RHS '{n}' has rank outside the one-rank E profile"
  | .arrayPart .. => .error "memory RHS part select is outside the one-rank E profile"
  | .fill bit =>
      match ctx with
      | some w => .ok (LVec.replicate w bit)
      | none => .error "fill expression has no destination width"
  | .unsupported "ConversionExpression:unsized-xz" payload =>
      evalMemEUnsizedXZ ctx payload
  | e =>
      if memEReadsArray e then
        .error "memory expression is not a direct cell read"
      else
        resToExcept (evalPure2 s.scalar (instExpr2 d.env d.elemWidths ctx e))

/-! ## Implicit event controls

Plain `always @*` is a waiting process (§9.4.2.2.2), unlike `always_comb`.
The parser retains its source body and the memory profile keeps that body
source-shaped.  Its sensitivity is therefore the values of the expressions
read by the body.  In particular, a read of `mem[i]` is sensitive to the
selected cell and to the index expression; treating the whole memory as one
signal would wake the process for an unrelated cell and is observably wrong.
The walkers below collect those parser expressions without lowering them.
-/

mutual

def memEReadExprs : PExpr → List PExpr
  | e@(.ident _) => [e]
  | e@(.arrayElem _ indices) => e :: memEReadExprsList indices
  | e@(.arrayPart _ indices _ a b) => e ::
      (memEReadExprsList indices ++ memEReadExprs a ++ memEReadExprs b)
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => memEReadExprs a
  | .binary _ a b | .bitSel a b | .repl a b => memEReadExprs a ++ memEReadExprs b
  | .partSel a b c | .ternary a b c =>
      memEReadExprs a ++ memEReadExprs b ++ memEReadExprs c
  | .concat xs => memEReadExprsList xs
  | .functionCall .. => []
  | .lit _ | .fill _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .unsupported .. => []

def memEReadExprsList : List PExpr → List PExpr
  | [] => []
  | e :: rest => memEReadExprs e ++ memEReadExprsList rest

def memELhsReadExprs : PLhs → List PExpr
  | .ident _ => []
  | .bitSel _ i => memEReadExprs i
  | .partSel _ a b => memEReadExprs a ++ memEReadExprs b
  | .concat xs => memELhsReadExprsList xs
  | .arrayElem _ indices => memEReadExprsList indices
  | .arrayPart _ indices _ a b =>
      memEReadExprsList indices ++ memEReadExprs a ++ memEReadExprs b

def memELhsReadExprsList : List PLhs → List PExpr
  | [] => []
  | lhs :: rest => memELhsReadExprs lhs ++ memELhsReadExprsList rest

def memEStmtReadExprs : PStmt → List PExpr
  | .blockingAssign _ e | .nbaAssign _ e => memEReadExprs e
  | .blockingAssignL lhs e | .nbaAssignL lhs e =>
      memELhsReadExprs lhs ++ memEReadExprs e
  | .ifStmt c yes no =>
      memEReadExprs c ++ memEStmtReadExprs yes ++ memEStmtReadExprsOpt no
  | .block body => memEStmtReadExprsList body
  | .forLoop _ init condition step body =>
      memEReadExprs init ++ memEReadExprs condition ++ memEReadExprs step ++
        memEStmtReadExprs body
  | .caseStmt subject items default? _ _ =>
      memEReadExprs subject ++ memECaseReadExprs items ++ memEStmtReadExprsOpt default?
  | .unsupported .. => []

def memEStmtReadExprsOpt : Option PStmt → List PExpr
  | none => []
  | some body => memEStmtReadExprs body

def memEStmtReadExprsList : List PStmt → List PExpr
  | [] => []
  | stmt :: rest => memEStmtReadExprs stmt ++ memEStmtReadExprsList rest

def memECaseReadExprs : List (List PExpr × PStmt) → List PExpr
  | [] => []
  | (patterns, body) :: rest =>
      memEReadExprsList patterns ++ memEStmtReadExprs body ++ memECaseReadExprs rest

end

def memEReadChanged (d : MemEDesign) (before after : MemEState) : List PExpr →
    Except String Bool
  | [] => .ok false
  | expr :: rest => do
      let old ← evalMemEExpr d before none expr
      let now ← evalMemEExpr d after none expr
      if old == now then memEReadChanged d before after rest else .ok true

def memETarget (d : MemEDesign) (s : MemEState) : PLhs → Except String (Option (String × Int))
  | .arrayElem n [idx] =>
      match d.memDecl? n with
      | none => .error s!"memory target '{n}' is not declared"
      | some _ => do
          let i? ← evalMemEIndex d s idx
          .ok (i?.map fun i => (n, i))
  | .arrayElem _ _ => .error "memory target has rank outside the one-rank E profile"
  | .arrayPart .. => .error "memory target part select is outside the one-rank E profile"
  | _ => .error "target is not an unpacked memory cell"

def MemEDesign.scalarWidth? (d : MemEDesign) (name : String) : Except String Nat :=
  match d.decls.find? (fun dc => dc.name == name) with
  | some dc => .ok dc.width
  | none => .error s!"scalar NBA target '{name}' is not a declared scalar"

abbrev MemEExec := Except String (MemEState × List MemEUpdate)

mutual

def execMemEForBody (d : MemEDesign) (s : MemEState) : PStmt → MemEExec
  | .nbaAssign name value => do
      let width ← d.scalarWidth? name
      let v ← evalMemEExpr d s (some width) value
      .ok (s, [.scalar name v])
  | .nbaAssignL target value => do
      let target? ← memETarget d s target
      match target? with
      | none => .ok (s, [])
      | some (name, index) =>
          let ctx ← match d.memDecl? name with
            | none => .error s!"memory target '{name}' is not declared"
            | some pd => (d.shape? pd).map (·.elemWidth)
          let v ← evalMemEExpr d s (some ctx) value
          .ok (s, [.cell name index v])
  | .ifStmt cond yes no => do
      let cv ← evalMemEExpr d s (some 1) cond
      if cv.condTrue then execMemEForBody d s yes else
        match no with
        | none => .ok (s, [])
        | some stmt => execMemEForBody d s stmt
  | .block body => execMemEForBodyList d s body
  | .blockingAssign _ _ | .blockingAssignL _ _ =>
      .error "E memory edge loop body requires an NBA assignment"
  | .caseStmt .. => .error "E memory edge loop case is outside the first memory profile"
  | .forLoop .. => .error "nested E memory edge loops are outside the first memory profile"
  | .unsupported k _ => .error s!"unsupported statement '{k}'"

def execMemEForBodyList (d : MemEDesign) (s : MemEState) : List PStmt → MemEExec
  | [] => .ok (s, [])
  | stmt :: rest => do
      let (s1, us) ← execMemEForBody d s stmt
      let (s2, vs) ← execMemEForBodyList d s1 rest
      .ok (s2, us ++ vs)

end

def memEHeaderEnv (env : IEnv) (condition : PExpr) : IEnv :=
  match condition with
  | .binary _ _ (.paramRef n none) =>
      match env.intVal? n with
      | some v => env.bindVal n v
      | none => env
  | _ => env

def execMemEFor (d : MemEDesign) (s : MemEState) (iterator : String)
    (init condition step : PExpr) (body : PStmt) : MemEExec := do
  let env0 := memEHeaderEnv d.env condition
  let schema ← match Loop2.headerSchema env0 iterator init condition step with
    | .ok schema => .ok schema
    | .error e => .error s!"E memory edge loop: {e}"
  -- A procedural `integer i;` iterator is retained in the loop header by the
  -- parser and is not a module declaration.  The source type is nevertheless
  -- the signed 32-bit `integer` type (§6.11), so it has a local 32-bit slot.
  let width := (d.decls.find? (fun dc => dc.name == iterator)).map (·.width) |>.getD 32
  let rec go : List Int → MemEState → MemEExec
    | [], state => .ok (state, [])
    | i :: rest, state => do
        let env := env0.bindVal iterator i
        let di := { d with env }
        let si := { state with scalar := SvState.set state.scalar iterator (LVec.ofInt width i) }
        let (sBody, us) ← execMemEForBody di si body
        let next ← match step with
          | .unary .inc (.genvarRef n) =>
              if n == iterator then .ok (i + 1)
              else .error "E memory edge loop step increments a different iterator"
          | .unary .dec (.genvarRef n) =>
              if n == iterator then .ok (i - 1)
              else .error "E memory edge loop step decrements a different iterator"
          | _ =>
              let nextVec ← evalMemEExpr di sBody (some width) step
              match nextVec.toInt? with
              | some next => .ok next
              | none => .error "E memory edge loop step is not a known integer"
        let sNext := { sBody with scalar := SvState.set sBody.scalar iterator (LVec.ofInt width next) }
        let (sTail, vs) ← go rest sNext
        .ok (sTail, us ++ vs)
  go schema.toList s

mutual

def execMemEStmt (d : MemEDesign) (s : MemEState) : PStmt → MemEExec
  | .nbaAssign name value => do
      let width ← d.scalarWidth? name
      let v ← evalMemEExpr d s (some width) value
      .ok (s, [.scalar name v])
  | .nbaAssignL target value => do
      let target? ← memETarget d s target
      match target? with
      | none => .ok (s, [])
      | some (name, index) =>
          let ctx ← match d.memDecl? name with
            | none => .error s!"memory target '{name}' is not declared"
            | some pd => (d.shape? pd).map (·.elemWidth)
          let v ← evalMemEExpr d s (some ctx) value
          .ok (s, [.cell name index v])
  | .ifStmt cond yes no => do
      let cv ← evalMemEExpr d s (some 1) cond
      if cv.condTrue then execMemEStmt d s yes else execMemEStmtOpt d s no
  | .block body => execMemEStmtList d s body
  | .blockingAssign _ _ | .blockingAssignL _ _ =>
      .error "E memory edge body requires an NBA assignment"
  | .caseStmt .. => .error "E memory edge case is outside the first memory profile"
  | .forLoop iterator init condition step body =>
      execMemEFor d s iterator init condition step body
  | .unsupported k _ => .error s!"unsupported statement '{k}'"

def execMemEStmtOpt (d : MemEDesign) (s : MemEState) : Option PStmt → MemEExec
  | none => .ok (s, [])
  | some body => execMemEStmt d s body

def execMemEStmtList (d : MemEDesign) (s : MemEState) : List PStmt → MemEExec
  | [] => .ok (s, [])
  | st :: rest => do
      let (s1, us) ← execMemEStmt d s st
      let (s2, vs) ← execMemEStmtList d s1 rest
      .ok (s2, us ++ vs)

end

def memEEvalExprs (d : MemEDesign) (s : MemEState) : List PExpr →
    Except String (List LVec)
  | [] => .ok []
  | expr :: rest => do
      let value ← evalMemEExpr d s none expr
      let tail ← memEEvalExprs d s rest
      .ok (value :: tail)

/-! Select one arm of a retained case in source order.  Selection is kept
separate from body execution so the body recursion remains structural over
the parser's `PStmt` node. -/

def memESelectCase (d : MemEDesign) (s : MemEState) (subject : LVec)
    (items : List (List PExpr × PStmt)) (default? : Option PStmt)
    (mode : CaseMode) : Except String (Option PStmt) :=
  match items with
  | [] => .ok default?
  | (patterns, body) :: rest => do
      let values ← memEEvalExprs d s patterns
      if values.any (fun value => caseHit mode subject value) then
        .ok (some body)
      else
        memESelectCase d s subject rest default? mode

/-! The first implicit-event case slice keeps arm execution deliberately
source-shaped and narrow: an arm may be one blocking scalar or cell assignment
(`begin end` with no statements is also harmless).  Rich arm bodies remain a
named boundary until the general procedural E walker is available. -/

def execMemECaseBody (d : MemEDesign) (s : MemEState) : PStmt →
    Except String MemEState
  | .blockingAssign name value => do
      let width ← d.scalarWidth? name
      let v ← evalMemEExpr d s (some width) value
      .ok { s with scalar := SvState.set s.scalar name v }
  | .blockingAssignL target value =>
      match target with
      | .arrayElem name [_idx] => do
          let some pd := d.memDecl? name
            | .error s!"memory target '{name}' is not declared"
          let target? ← memETarget d s target
          match target? with
          | none => .ok s
          | some (memName, index) => do
              let ctx ← (d.shape? pd).map (·.elemWidth)
              let v ← evalMemEExpr d s (some ctx) value
              match s.memory.write memName index v with
              | some memory => .ok { s with memory }
              | none => .error s!"memory '{memName}' is not present in E state"
      | _ => .error "E implicit case arm target is outside the source-shaped memory profile"
  | .block [] => .ok s
  | _ => .error "E implicit case arm body is outside the current memory profile"

def memECaseBodyAdmission : PStmt → Except String Unit
  | .blockingAssign _ _ | .blockingAssignL _ _ | .block [] => .ok ()
  | _ => .error "E implicit case arm body is outside the current memory profile"

/-! Execute one activation of a retained plain `always @*` body.  The body is
blocking by construction; NBA statements belong to edge processes and remain
a loud boundary here.  Case arms are walked in source order and use the
parser's `CaseMode`/`caseHit`, so this is the case node's own rule rather than
an if-chain lowering. -/

mutual

def execMemEImplicitBody (d : MemEDesign) (s : MemEState) : PStmt →
    Except String MemEState
  | .blockingAssign name value => do
      let width ← d.scalarWidth? name
      let v ← evalMemEExpr d s (some width) value
      .ok { s with scalar := SvState.set s.scalar name v }
  | .blockingAssignL target value =>
      match target with
      | .arrayElem name [_idx] => do
          let some pd := d.memDecl? name
            | .error s!"memory target '{name}' is not declared"
          let target? ← memETarget d s target
          match target? with
          | none => .ok s
          | some (memName, index) => do
              let ctx ← (d.shape? pd).map (·.elemWidth)
              let v ← evalMemEExpr d s (some ctx) value
              match s.memory.write memName index v with
              | some memory => .ok { s with memory }
              | none => .error s!"memory '{memName}' is not present in E state"
      | _ => .error "E implicit body target is outside the source-shaped memory profile"
  | .ifStmt cond yes no => do
      let cv ← evalMemEExpr d s (some 1) cond
      if cv.condTrue then execMemEImplicitBody d s yes else
        execMemEImplicitBodyOpt d s no
  | .block body => execMemEImplicitBodyList d s body
  | .caseStmt subject items default? mode _check => do
      let sv ← evalMemEExpr d s none subject
      let selected ← memESelectCase d s sv items default? mode
      match selected with
      | none => .ok s
      | some body => execMemECaseBody d s body
  | .forLoop .. => .error "E implicit body procedural loops are outside the memory profile"
  | .nbaAssign .. | .nbaAssignL .. =>
      .error "E implicit body requires blocking assignments"
  | .unsupported k _ => .error s!"unsupported statement '{k}'"
termination_by structural stmt => stmt

def execMemEImplicitBodyOpt (d : MemEDesign) (s : MemEState) : Option PStmt →
    Except String MemEState
  | none => .ok s
  | some body => execMemEImplicitBody d s body
termination_by structural opt => opt

def execMemEImplicitBodyList (d : MemEDesign) (s : MemEState) : List PStmt →
    Except String MemEState
  | [] => .ok s
  | stmt :: rest => do
      let s' ← execMemEImplicitBody d s stmt
      execMemEImplicitBodyList d s' rest
termination_by structural stmts => stmts

end

/-! Admission mirrors the executable process dispatch above.  `execMemEEdge`
and `execMemEAssign` are deliberately total over `PProcess`, so a missing arm
would otherwise be a silent skip.  Check every retained process before
building the design and keep the source-shaped statement boundary loud. -/

mutual

def memEImplicitBodyAdmission : PStmt → Except String Unit
  | .blockingAssign _ _ | .blockingAssignL _ _ => .ok ()
  | .ifStmt _ yes no => do
      memEImplicitBodyAdmission yes
      match no with
      | none => .ok ()
      | some body => memEImplicitBodyAdmission body
  | .block body => memEImplicitBodyListAdmission body
  | .caseStmt _ items default? _mode _check => do
      memEImplicitCaseItemsAdmission items
      match default? with
      | none => .ok ()
      | some body => memECaseBodyAdmission body
  | .forLoop .. =>
      .error "E implicit body procedural loops are outside the current memory profile"
  | .nbaAssign .. | .nbaAssignL .. =>
      .error "E implicit body requires blocking assignments"
  | .unsupported k _ => .error s!"unsupported statement '{k}'"

def memEImplicitBodyListAdmission : List PStmt → Except String Unit
  | [] => .ok ()
  | stmt :: rest => do
      memEImplicitBodyAdmission stmt
      memEImplicitBodyListAdmission rest

def memEImplicitBodyItemsAdmission : List (List PExpr × PStmt) → Except String Unit
  | [] => .ok ()
  | (_, body) :: rest => do
      memEImplicitBodyAdmission body
      memEImplicitBodyItemsAdmission rest

def memEImplicitCaseItemsAdmission : List (List PExpr × PStmt) → Except String Unit
  | [] => .ok ()
  | (_, body) :: rest => do
      memECaseBodyAdmission body
      memEImplicitCaseItemsAdmission rest

def memEForBodyAdmission : PStmt → Except String Unit
  | .nbaAssign _ _ | .nbaAssignL _ _ => .ok ()
  | .ifStmt _ yes no => do
      memEForBodyAdmission yes
      match no with
      | none => .ok ()
      | some body => memEForBodyAdmission body
  | .block body => memEForBodyListAdmission body
  | .blockingAssign .. | .blockingAssignL .. =>
      .error "E memory edge loop body requires an NBA assignment"
  | .caseStmt .. => .error "E memory edge loop case is outside the first memory profile"
  | .forLoop .. => .error "nested E memory edge loops are outside the first memory profile"
  | .unsupported k _ => .error s!"unsupported statement '{k}'"

def memEForBodyListAdmission : List PStmt → Except String Unit
  | [] => .ok ()
  | stmt :: rest => do
      memEForBodyAdmission stmt
      memEForBodyListAdmission rest

def memEEdgeBodyAdmission : PStmt → Except String Unit
  | .nbaAssign _ _ | .nbaAssignL _ _ => .ok ()
  | .ifStmt _ yes no => do
      memEEdgeBodyAdmission yes
      match no with
      | none => .ok ()
      | some body => memEEdgeBodyAdmission body
  | .block body => memEEdgeBodyListAdmission body
  | .forLoop _ _ _ _ body => memEForBodyAdmission body
  | .blockingAssign .. | .blockingAssignL .. =>
      .error "E memory edge body requires an NBA assignment"
  | .caseStmt .. => .error "E memory edge case is outside the first memory profile"
  | .unsupported k _ => .error s!"unsupported statement '{k}'"

def memEEdgeBodyListAdmission : List PStmt → Except String Unit
  | [] => .ok ()
  | stmt :: rest => do
      memEEdgeBodyAdmission stmt
      memEEdgeBodyListAdmission rest

end

def memEProcessAdmission : PProcess → Except String Unit
  | .alwaysFF _ body | .alwaysPlain _ body => memEEdgeBodyAdmission body
  | .alwaysFFR _ _ body false => memEEdgeBodyAdmission body
  | .alwaysFFR _ _ _ true =>
      .error "E memory route does not yet admit active-high asynchronous reset events"
  | .alwaysImplicit body => memEImplicitBodyAdmission body
  | .assign _ _ => .ok ()
  | .assignL _ _ =>
      .error "E memory route does not yet admit select-target continuous assignments"
  | .alwaysComb _ =>
      .error "E memory route does not yet admit always_comb processes"
  | .initial _ => .ok ()
  | .unsupported k text => .error s!"unsupported process '{k}': {text}"

def memEProcessAdmissions : List PProcess → Except String Unit
  | [] => .ok ()
  | p :: rest => do
      memEProcessAdmission p
      memEProcessAdmissions rest

/-! A source-shaped active pass.  It evaluates every continuous assignment as
the existing memory profile did, then wakes each retained implicit process
whose parser-derived read expression changed.  A body is run at most once in
this pass; a body that changes one of its own watched reads is rejected rather
than silently dropping the re-arm that a full event scheduler would perform.
This is the acyclic scheduler slice used by the memory profile; cyclic or
multi-pass event graphs remain loud. -/

def memEImplicitPass (d : MemEDesign) (before : MemEState) (current : MemEState) :
    List PProcess → Except String MemEState
  | [] => .ok current
  | .alwaysImplicit body :: rest => do
      let watched := memEStmtReadExprs body
      let ready ← memEReadChanged d before current watched
      if !ready then
        memEImplicitPass d before current rest
      else
        let after ← execMemEImplicitBody d current body
        let rearmed ← memEReadChanged d current after watched
        if rearmed then
          .error "E implicit event process re-triggered in one active pass"
        else
          memEImplicitPass d before after rest
  | _ :: rest => memEImplicitPass d before current rest

def commitMemE (s : MemEState) : List MemEUpdate → Except String MemEState
  | [] => .ok s
  | .scalar n v :: rest =>
      commitMemE { s with scalar := SvState.set s.scalar n v } rest
  | .cell n i v :: rest =>
      match s.memory.write n i v with
      | none => .error s!"memory '{n}' is not present in E state"
      | some m => commitMemE { s with memory := m } rest

def MemEDesign.initialBodies : List PProcess → List PStmt
  | [] => []
  | .initial body :: rest => body :: MemEDesign.initialBodies rest
  | _ :: rest => MemEDesign.initialBodies rest

def MemEDesign.readmemhBodyCount : PStmt → Option Nat
  | .unsupported "SystemTask:readmemh" _ => some 1
  | .block body =>
      body.foldlM (init := 0) fun n stmt => do
        let k ← MemEDesign.readmemhBodyCount stmt
        return n + k
  | _ => none

/-! The parser's structured `$readmemh` task is a time-zero memory write.  The
    only initial process admitted here is the one source-shaped task body that
    accompanies that metadata; every other initial form stays loud.  Multiple
    initials are refused because §4.7 leaves their Active-region order open. -/
def MemEDesign.timeZero (d : MemEDesign) : Except String MemEState := do
  let bodies := MemEDesign.initialBodies d.processes
  match bodies with
  | [] =>
      if d.readmemh.isEmpty then .ok d.init
      else .error "SystemTask:readmemh metadata has no initial process"
  | [body] =>
      match MemEDesign.readmemhBodyCount body with
      | some count =>
          if count != d.readmemh.length || count == 0 then
            .error "SystemTask:readmemh metadata does not match the initial process"
          else d.writeReadmemhList d.init d.readmemh
      | none =>
          if !d.readmemh.isEmpty then
            .error "SystemTask:readmemh metadata does not match the initial process"
          else do
            let (_, updates) ← execMemEStmt d d.init body
            commitMemE d.init updates
  | _ => .error "memory E time-zero route does not yet admit multiple initial processes"

def edgeFires (p : PProcess) (old now : SvState) : Bool :=
  match p with
  | .alwaysFF clk _ | .alwaysPlain clk _ => isPosedge (old.bit0 clk) (now.bit0 clk)
  | .alwaysFFR clk rstn _ false =>
      isPosedge (old.bit0 clk) (now.bit0 clk) || isNegedge (old.bit0 rstn) (now.bit0 rstn)
  | _ => false

def execMemEEdge (d : MemEDesign) (old now : SvState) (s : MemEState) :
    List PProcess → Except String (List MemEUpdate)
  | [] => .ok []
  | p :: ps => do
      let here ← match p with
        | .alwaysFF _ body | .alwaysPlain _ body | .alwaysFFR _ _ body false =>
            if edgeFires p old now then execMemEStmt d s body else .ok (s, [])
        | _ => .ok (s, [])
      let (_, hereUpdates) := here
      let rest ← execMemEEdge d old now s ps
      .ok (hereUpdates ++ rest)

def execMemEAssign (d : MemEDesign) (s : MemEState) : List PProcess → Except String MemEState
  | [] => .ok s
  | .assign name value :: ps => do
      let ctx := (d.decls.find? (fun dc => dc.name == name)).map (fun dc => dc.width)
      let v ← evalMemEExpr d s ctx value
      execMemEAssign d { s with scalar := SvState.set s.scalar name v } ps
  | _ :: ps => execMemEAssign d s ps

/-- One source-shaped E memory cycle: apply inputs, issue edge NBAs from the
 pre-edge state, commit them, then settle direct continuous cell reads. -/
def MemEDesign.step (d : MemEDesign) (s : MemEState) (inputs : SvState) : Except String MemEState := do
  let sIn := d.applyInputs inputs s
  let sPre ← if d.preSettle then
      execMemEAssign d sIn d.processes
    else .ok sIn
  let us ← execMemEEdge d s.scalar sPre.scalar sPre d.processes
  let s' ← commitMemE sPre us
  let s'' ← execMemEAssign d s' d.processes
  -- Sensitivity is measured against the complete pre-slot state: input
  -- changes, edge commits, and continuous assignments all create events.
  memEImplicitPass d s s'' d.processes

def MemEDesign.ofPDesign (d : PDesign) (args : List Int) : Res MemEDesign := do
  let env ← d.paramEnv2 args
  if d.others.any (fun entry => !memEAllowedOther entry) then
    .unsupported "E memory route does not yet admit unsupported module members"
  match memEProcessAdmissions d.processes with
  | .ok () => pure ()
  | .error e => .unsupported e
  let rec decls : List PDecl → Res (List Decl)
    | [] => .ok []
    | pd :: rest => do
        if !pd.unpackedDims.isEmpty then decls rest
        else
          match pd.type.width env with
          | .error e => .unsupported e
          | .ok w => do
              let dc : Decl := ⟨pd.name, w, pd.isSigned, pd.twoState,
                pd.isInput, pd.isOutput, pd.isNet, none⟩
              let tail ← decls rest
              .ok (dc :: tail)
  let ds ← decls d.decls
  let ds := ds ++ memEOtherDecls d.others
  let envD := { env with widths := ds.map (fun dc => (dc.name, dc.width)) }
  /- The symbolic frontend's fixed unpacked cells carry the source array name
     and label as metadata.  Reconstitute that declaration node for the
     canonical MemState shape; the cells remain the sourceDecls witness and
     are never used as a second storage representation. -/
  let fixedBases := d.decls.foldl (fun bases pd =>
    match pd.flatBase with
    | some base => if bases.any (· == base) then bases else bases ++ [base]
    | none => bases) []
  let fixedMemDecls := fixedBases.filterMap fun base =>
    match d.decls.find? (fun pd => pd.flatBase == some base) with
    | none => none
    | some firstDecl =>
        let cells := d.decls.filter (fun pd => pd.flatBase == some base)
        let first := firstDecl.flatIndex.getD 0
        let last := (cells.getLast?.bind (·.flatIndex)).getD first
        some { firstDecl with
          name := base
          unpackedDims := [{ msb := PExpr.int first, lsb := PExpr.int last }]
          flatBase := none
          flatIndex := none }
  let mems := d.decls.filter (fun pd => !pd.unpackedDims.isEmpty) ++ fixedMemDecls
  match d.memShapesAt envD with
  | .ok _ => pure ()
  | .error e => .unsupported e
  let result : MemEDesign :=
    { name := d.name, env := envD, decls := ds, memDecls := mems,
      processes := d.processes, others := d.others,
      readmemh := d.readmemh, sourceDecls := d.decls }
  match result.memoryOrderReport with
  | none => .ok result
  | some (kind, msg) => .unsupported s!"{kind}: {msg}"

end Kernel

#print axioms LeanModels.Sv.Kernel.MemEDesign.step
