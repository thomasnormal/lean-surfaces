import LeanModels.Sv.PreemptGuard2
import LeanModels.Sv.MemCycle

/-!
# IEEE §4.7 guard for the source-shaped memory route

`MemCycle` keeps unpacked arrays as `MemState` cells and therefore cannot use
the flat `Design2` access walk.  This guard is the corresponding source-shaped
walk.  A memory access is conservatively represented by the whole named
memory: a dynamic index can alias any cell, while a fixed index remains in the
parser-shaped `PExpr.arrayElem`/`PLhs.arrayElem` node.  The route is admitted
only when every cross-process read/write or write/write overlap is hidden by
the same safe activation rule as the semantic route: NBA-only edge bodies and
one-shot continuous assignments.

This is a route boundary, not a new executor.  `runMem2` remains unchanged;
the runner checks the report before it calls the memory cycle.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv
open LeanModels.Sv.CombGuard

def MemDesign2.preemptWidth? (d : MemDesign2) (name : String) : Option Nat :=
  match d.decls.find? (·.name == name) with
  | some dc => some dc.width
  | none =>
      match d.memDecls.find? (·.name == name) with
      | some pd =>
          match pd.memShape? d.env with
          | .ok (some shape) => some shape.elemWidth
          | _ => none
      | none =>
          match d.flatCellInfo? name with
          | some (base, _) =>
              match d.flatCellWidth? base with
              | some w => some w
              | none => none
          | none => none

def MemDesign2.preemptWd (d : MemDesign2) (name : String) : Option Nat :=
  match d.flatCellInfo? name with
  | some (base, _) => d.preemptWidth? base |>.orElse (fun _ => d.preemptWidth? name)
  | none => d.preemptWidth? name

def memPreemptWhole (d : MemDesign2) (name : String) : List BWin :=
  match d.preemptWd name with
  | some w =>
      match d.flatCellInfo? name with
      | some (base, _) => [(base, 0, w)]
      | none => [(name, 0, w)]
  | none => []

end LeanModels.Sv.Kernel

namespace LeanModels.Sv

open CombGuard
open Kernel

mutual
  def PExpr.memPreemptReads (d : MemDesign2) : PExpr → List BWin
    | .lit _ | .paramRef _ _ | .genvarRef _ | .enumRef _ _ _ | .int _
    | .fill _ | .unsupported _ _ => []
    | .ident n => memPreemptWhole d n
    | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
    | .sysCall _ a | .reduce _ a | .cast _ a => PExpr.memPreemptReads d a
    | .binary _ a b | .bitSel a b | .repl a b =>
        PExpr.memPreemptReads d a ++ PExpr.memPreemptReads d b
    | .ternary c a b | .partSel c a b =>
        PExpr.memPreemptReads d c ++ PExpr.memPreemptReads d a ++
          PExpr.memPreemptReads d b
    | .concat xs => PExpr.memPreemptReadsList d xs
    | .arrayElem n xs =>
        memPreemptWhole d n ++ PExpr.memPreemptReadsList d xs
    | .arrayPart n xs _ a b =>
        memPreemptWhole d n ++ PExpr.memPreemptReadsList d xs ++
          PExpr.memPreemptReads d a ++ PExpr.memPreemptReads d b
    termination_by structural e => e

  def PExpr.memPreemptReadsList (d : MemDesign2) : List PExpr → List BWin
    | [] => []
    | x :: xs =>
        PExpr.memPreemptReads d x ++ PExpr.memPreemptReadsList d xs
    termination_by structural xs => xs
end

mutual
  def PLhs.memPreemptReads (d : MemDesign2) : PLhs → List BWin
    | .ident _ => []
    | .bitSel _ i => PExpr.memPreemptReads d i
    | .partSel _ a b => PExpr.memPreemptReads d a ++ PExpr.memPreemptReads d b
    | .concat xs => PLhs.memPreemptReadsList d xs
    | .arrayElem _ xs => PExpr.memPreemptReadsList d xs
    | .arrayPart _ xs _ a b =>
        PExpr.memPreemptReadsList d xs ++ PExpr.memPreemptReads d a ++
          PExpr.memPreemptReads d b
    termination_by structural l => l

  def PLhs.memPreemptReadsList (d : MemDesign2) : List PLhs → List BWin
    | [] => []
    | x :: xs =>
        PLhs.memPreemptReads d x ++ PLhs.memPreemptReadsList d xs
    termination_by structural xs => xs
end

mutual
  def PLhs.memPreemptWrites (d : MemDesign2) : PLhs → List BWin
    | .ident n | .bitSel n _ | .partSel n _ _ | .arrayElem n _ | .arrayPart n .. =>
        memPreemptWhole d n
    | .concat xs => PLhs.memPreemptWritesList d xs
    termination_by structural l => l

  def PLhs.memPreemptWritesList (d : MemDesign2) : List PLhs → List BWin
    | [] => []
    | x :: xs =>
        PLhs.memPreemptWrites d x ++ PLhs.memPreemptWritesList d xs
    termination_by structural xs => xs
end

mutual
  def PStmt.memPreemptReads (d : MemDesign2) : PStmt → List BWin
    | .blockingAssign n e | .nbaAssign n e =>
        memPreemptWhole d n ++ PExpr.memPreemptReads d e
    | .ifStmt c t e =>
        PExpr.memPreemptReads d c ++ PStmt.memPreemptReads d t ++
          PStmt.memPreemptReadsOpt d e
    | .block xs => PStmt.memPreemptReadsList d xs
    | .forLoop _ i c s b =>
        PExpr.memPreemptReads d i ++ PExpr.memPreemptReads d c ++
          PExpr.memPreemptReads d s ++ PStmt.memPreemptReads d b
    | .blockingAssignL l e | .nbaAssignL l e =>
        PLhs.memPreemptReads d l ++ PExpr.memPreemptReads d e
    | .caseStmt s items defaultBody _ _ =>
        PExpr.memPreemptReads d s ++ PStmt.memPreemptReadsItems d items ++
          PStmt.memPreemptReadsOpt d defaultBody
    | .unsupported _ _ => []
    termination_by structural s => s

  def PStmt.memPreemptReadsOpt (d : MemDesign2) : Option PStmt → List BWin
    | none => []
    | some s => PStmt.memPreemptReads d s
    termination_by structural o => o

  def PStmt.memPreemptReadsList (d : MemDesign2) : List PStmt → List BWin
    | [] => []
    | s :: ss =>
        PStmt.memPreemptReads d s ++ PStmt.memPreemptReadsList d ss
    termination_by structural xs => xs

  def PStmt.memPreemptReadsItems (d : MemDesign2) :
      List (List PExpr × PStmt) → List BWin
    | [] => []
    | (patterns, body) :: rest =>
        PExpr.memPreemptReadsList d patterns ++ PStmt.memPreemptReads d body ++
          PStmt.memPreemptReadsItems d rest
    termination_by structural xs => xs
end

mutual
  def PStmt.memPreemptWrites (d : MemDesign2) : PStmt → List BWin
    | .blockingAssign n _ | .nbaAssign n _ => memPreemptWhole d n
    | .ifStmt _ t e =>
        PStmt.memPreemptWrites d t ++ PStmt.memPreemptWritesOpt d e
    | .block xs => PStmt.memPreemptWritesList d xs
    | .forLoop _ _ _ _ b => PStmt.memPreemptWrites d b
    | .blockingAssignL l _ | .nbaAssignL l _ => PLhs.memPreemptWrites d l
    | .caseStmt _ items defaultBody _ _ =>
        PStmt.memPreemptWritesItems d items ++
          PStmt.memPreemptWritesOpt d defaultBody
    | .unsupported _ _ => []
    termination_by structural s => s

  def PStmt.memPreemptWritesOpt (d : MemDesign2) : Option PStmt → List BWin
    | none => []
    | some s => PStmt.memPreemptWrites d s
    termination_by structural o => o

  def PStmt.memPreemptWritesList (d : MemDesign2) : List PStmt → List BWin
    | [] => []
    | s :: ss =>
        PStmt.memPreemptWrites d s ++ PStmt.memPreemptWritesList d ss
    termination_by structural xs => xs

  def PStmt.memPreemptWritesItems (d : MemDesign2) :
      List (List PExpr × PStmt) → List BWin
    | [] => []
    | (_, body) :: rest =>
        PStmt.memPreemptWrites d body ++ PStmt.memPreemptWritesItems d rest
    termination_by structural xs => xs
end

mutual
  def PStmt.memPreemptNBAOnly : PStmt → Bool
    | .nbaAssign _ _ | .nbaAssignL _ _ => true
    | .blockingAssign _ _ | .blockingAssignL _ _ | .forLoop _ _ _ _ _ => false
    | .ifStmt _ t e =>
        PStmt.memPreemptNBAOnly t && PStmt.memPreemptNBAOnlyOpt e
    | .block xs => PStmt.memPreemptNBAOnlyList xs
    | .caseStmt _ items defaultBody _ _ =>
        PStmt.memPreemptNBAOnlyItems items &&
          PStmt.memPreemptNBAOnlyOpt defaultBody
    | .unsupported _ _ => false
    termination_by structural s => s

  def PStmt.memPreemptNBAOnlyOpt : Option PStmt → Bool
    | none => true
    | some s => PStmt.memPreemptNBAOnly s
    termination_by structural o => o

  def PStmt.memPreemptNBAOnlyList : List PStmt → Bool
    | [] => true
    | s :: ss => PStmt.memPreemptNBAOnly s && PStmt.memPreemptNBAOnlyList ss
    termination_by structural xs => xs

  def PStmt.memPreemptNBAOnlyItems : List (List PExpr × PStmt) → Bool
    | [] => true
    | (_, body) :: rest =>
        PStmt.memPreemptNBAOnly body && PStmt.memPreemptNBAOnlyItems rest
    termination_by structural xs => xs
end

def PProcess.memPreemptAtomic : PProcess → Bool
  | .assign _ _ | .assignL _ _ => true
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysFFR _ _ b _ =>
      PStmt.memPreemptNBAOnly b
  | _ => false

def PProcess.memPreemptAccess (d : MemDesign2) : PProcess → ProcessAccess
  | .assign n e => (PExpr.memPreemptReads d e, memPreemptWhole d n)
  | .assignL l e =>
      (PLhs.memPreemptReads d l ++ PExpr.memPreemptReads d e,
       PLhs.memPreemptWrites d l)
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysFFR _ _ b _ =>
      (PStmt.memPreemptReads d b, PStmt.memPreemptWrites d b)
  | .alwaysComb b | .initial b =>
      (PStmt.memPreemptReads d b, PStmt.memPreemptWrites d b)
  | .unsupported _ _ => ([], [])

namespace Kernel

def MemDesign2.memoryPreemptionReport (d : MemDesign2) : Option (String × String) :=
  let accesses := d.processes.map fun p =>
    (PProcess.memPreemptAtomic p, PProcess.memPreemptAccess d p)
  match LeanModels.Sv.firstPreemptUnsafe accesses 0 with
  | none => none
  | some (i, j) =>
      some ("Schedule:preemptive",
        s!"processes {i} and {j} may observe an intermediate write under IEEE 1800-2023 §4.7; the memory route requires disjoint cross-process read/write windows")

def MemDesign2.memoryPreemptionAdmits (d : MemDesign2) : Bool := d.memoryPreemptionReport.isNone

end Kernel
end LeanModels.Sv

#print axioms LeanModels.Sv.Kernel.MemDesign2.memoryPreemptionReport
