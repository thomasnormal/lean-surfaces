import LeanModels.Sv.Kernel.Core1Edge
import LeanModels.Sv.Kernel.MemElab
import LeanModels.Sv.Gen2

/-!
# The first source-shaped memory step in E

This is the small E memory profile used by the Carnot FIFO wall.  It keeps
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

set_option autoImplicit false

structure MemEDesign where
  name : String
  env : IEnv
  decls : List Decl
  memDecls : List PDecl
  processes : List PProcess
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
      (dc.name, dc.init.getD (if dc.isNet then LVec.replicate dc.width .lz
        else LVec.xVec dc.width)))
    memory := MemState.ofShapes (d.memDecls.filterMap fun pd =>
      match pd.memShape? d.env with
      | .ok (some shape) => some shape
      | _ => none) }

def MemEDesign.applyInputs (d : MemEDesign) (inputs : SvState) (s : MemEState) : MemEState :=
  { s with scalar := d.decls.foldl (fun st dc =>
      if dc.isInput then
        match SvState.lookup inputs dc.name with
        | some v => SvState.set st dc.name (if dc.twoState then v.toTwoState else v)
        | none => st
      else st) s.scalar }

mutual

def memEReadsArray : PExpr → Bool
  | .arrayElem .. | .arrayPart .. => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => memEReadsArray a
  | .binary _ a b | .bitSel a b | .repl a b => memEReadsArray a || memEReadsArray b
  | .partSel a b c | .ternary a b c => memEReadsArray a || memEReadsArray b || memEReadsArray c
  | .concat xs => memEReadsArrayList xs
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
  | e =>
      if memEReadsArray e then
        .error "memory expression is not a direct cell read"
      else
        resToExcept (evalPure2 s.scalar (instExpr2 d.env d.elemWidths ctx e))

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

mutual

def execMemEStmt (d : MemEDesign) (s : MemEState) : PStmt → Except String (List MemEUpdate)
  | .nbaAssign name value => do
      let width ← d.scalarWidth? name
      let v ← evalMemEExpr d s (some width) value
      .ok [.scalar name v]
  | .nbaAssignL target value => do
      let target? ← memETarget d s target
      match target? with
      | none => .ok []
      | some (name, index) =>
          let ctx ← match d.memDecl? name with
            | none => .error s!"memory target '{name}' is not declared"
            | some pd => (d.shape? pd).map (·.elemWidth)
          let v ← evalMemEExpr d s (some ctx) value
          .ok [.cell name index v]
  | .ifStmt cond yes no => do
      let cv ← evalMemEExpr d s (some 1) cond
      if cv.condTrue then execMemEStmt d s yes else execMemEStmtOpt d s no
  | .block body => execMemEStmtList d s body
  | .blockingAssign _ _ | .blockingAssignL _ _ =>
      .error "E memory edge body requires an NBA assignment"
  | .caseStmt .. => .error "E memory edge case is outside the first memory profile"
  | .forLoop .. => .error "E memory edge loop is outside the first memory profile"
  | .unsupported k _ => .error s!"unsupported statement '{k}'"

def execMemEStmtOpt (d : MemEDesign) (s : MemEState) : Option PStmt → Except String (List MemEUpdate)
  | none => .ok []
  | some body => execMemEStmt d s body

def execMemEStmtList (d : MemEDesign) (s : MemEState) : List PStmt → Except String (List MemEUpdate)
  | [] => .ok []
  | st :: rest => do
      let us ← execMemEStmt d s st
      let vs ← execMemEStmtList d s rest
      .ok (us ++ vs)

end

def commitMemE (s : MemEState) : List MemEUpdate → Except String MemEState
  | [] => .ok s
  | .scalar n v :: rest =>
      commitMemE { s with scalar := SvState.set s.scalar n v } rest
  | .cell n i v :: rest =>
      match s.memory.write n i v with
      | none => .error s!"memory '{n}' is not present in E state"
      | some m => commitMemE { s with memory := m } rest

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
            if edgeFires p old now then execMemEStmt d s body else .ok []
        | _ => .ok []
      let rest ← execMemEEdge d old now s ps
      .ok (here ++ rest)

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
  let us ← execMemEEdge d s.scalar sIn.scalar sIn d.processes
  let s' ← commitMemE sIn us
  execMemEAssign d s' d.processes

def MemEDesign.ofPDesign (d : PDesign) (args : List Int) : Res MemEDesign := do
  let env ← d.paramEnv2 args
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
  let mems := d.decls.filter fun pd => !pd.unpackedDims.isEmpty
  match d.memShapesAt env with
  | .ok _ => pure ()
  | .error e => .unsupported e
  .ok ⟨d.name, env, ds, mems, d.processes⟩

end Kernel

#print axioms LeanModels.Sv.Kernel.MemEDesign.step
