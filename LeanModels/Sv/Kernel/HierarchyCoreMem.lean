import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Hier2

/-!
# One source-shaped memory hierarchy in canonical E

Module elaboration follows the parser's `PDesign`/`PInst` nodes and the
IEEE 1800-2023 §23.3.3 port-connection rule. A one-child source-shaped
hierarchy is merged into one `CoreMemDesign` while retaining declaration
identities, unpacked dimensions, loop bodies, and NBA timing. The executor is
the existing canonical `MemState`/`MemNbaQueue` route; no MemE adapter,
Design2 lowering, cell expansion, or second memory store is introduced.
-/
namespace LeanModels.Sv.Kernel
open LeanModels.Sv
set_option autoImplicit false

private def hExpr (pfx : String) : PExpr → PExpr
  | .ident n => .ident (pfx ++ n)
  | .arrayElem n is => .arrayElem (pfx ++ n) (is.map (hExpr pfx))
  | .arrayPart n is m a b => .arrayPart (pfx ++ n) (is.map (hExpr pfx)) m (hExpr pfx a) (hExpr pfx b)
  | .bitSel a b => .bitSel (hExpr pfx a) (hExpr pfx b)
  | .partSel a b c => .partSel (hExpr pfx a) (hExpr pfx b) (hExpr pfx c)
  | .unary o a => .unary o (hExpr pfx a)
  | .binary o a b => .binary o (hExpr pfx a) (hExpr pfx b)
  | .ternary a b c => .ternary (hExpr pfx a) (hExpr pfx b) (hExpr pfx c)
  | .concat xs => .concat (xs.map (hExpr pfx))
  | .resize w a => .resize w (hExpr pfx a)
  | .signedResize w a => .signedResize w (hExpr pfx a)
  | .squash2 w a => .squash2 w (hExpr pfx a)
  | .sysCall f a => .sysCall f (hExpr pfx a)
  | .reduce o a => .reduce o (hExpr pfx a)
  | .cast s a => .cast s (hExpr pfx a)
  | .repl n a => .repl (hExpr pfx n) (hExpr pfx a)
  | .functionCall n xs => .functionCall n (xs.map (hExpr pfx))
  | e@(.paramRef ..) | e@(.genvarRef ..) | e@(.enumRef ..)
  | e@(.int ..) | e@(.fill ..) | e@(.lit ..) | e@(.unsupported ..) => e

private def hLhs (pfx : String) : PLhs → PLhs
  | .ident n => .ident (pfx ++ n)
  | .bitSel n i => .bitSel (pfx ++ n) (hExpr pfx i)
  | .partSel n a b => .partSel (pfx ++ n) (hExpr pfx a) (hExpr pfx b)
  | .arrayElem n is => .arrayElem (pfx ++ n) (is.map (hExpr pfx))
  | .arrayPart n is m a b => .arrayPart (pfx ++ n) (is.map (hExpr pfx)) m (hExpr pfx a) (hExpr pfx b)
  | .concat xs => .concat (xs.map (hLhs pfx))

private partial def hStmt (pfx : String) : PStmt → PStmt
  | .blockingAssign n e => .blockingAssign (pfx ++ n) (hExpr pfx e)
  | .nbaAssign n e => .nbaAssign (pfx ++ n) (hExpr pfx e)
  | .blockingAssignL l e => .blockingAssignL (hLhs pfx l) (hExpr pfx e)
  | .nbaAssignL l e => .nbaAssignL (hLhs pfx l) (hExpr pfx e)
  | .ifStmt c a b => .ifStmt (hExpr pfx c) (hStmt pfx a) (b.map (hStmt pfx))
  | .block xs => .block (xs.map (hStmt pfx))
  | .forLoop i a c s b => .forLoop i (hExpr pfx a) (hExpr pfx c) (hExpr pfx s) (hStmt pfx b)
  | .caseStmt e xs d m c => .caseStmt (hExpr pfx e)
      (xs.map fun (ps, b) => (ps.map (hExpr pfx), hStmt pfx b))
      (d.map (hStmt pfx)) m c
  | e@(.unsupported ..) => e


private def hProcess (pfx : String) (clockMap : List (String × String)) : PProcess → PProcess
  | .alwaysFF c b => .alwaysFF (clockMap.lookup c |>.getD (pfx ++ c)) (hStmt pfx b)
  | .alwaysPlain c b => .alwaysPlain (clockMap.lookup c |>.getD (pfx ++ c)) (hStmt pfx b)
  | .alwaysComb b => .alwaysComb (hStmt pfx b)
  | .alwaysImplicit b => .alwaysImplicit (hStmt pfx b)
  | .alwaysFFR c r b hi => .alwaysFFR (clockMap.lookup c |>.getD (pfx ++ c))
      (clockMap.lookup r |>.getD (pfx ++ r)) (hStmt pfx b) hi
  | .assign n e => .assign (pfx ++ n) (hExpr pfx e)
  | .assignL l e => .assignL (hLhs pfx l) (hExpr pfx e)
  | .initial b => .initial (hStmt pfx b)
  | e@(.unsupported ..) => e

private def hItems : List GenItem → Option PInst
  | [] => none
  | .inst i :: _ => some i
  | .process _ :: rest | .unsupported .. :: rest => hItems rest
  | _ :: rest => hItems rest
termination_by structural xs => xs

private def childDesign (top : PDesign) (lib : List PDesign) (args : List Int) :
    Except String (PDesign × PInst × String) := do
  let env ← match top.paramEnvH { int32 := true } args with
    | .ok e => pure e
    | .timeout => throw "parameter elaboration timed out"
    | .unsupported e => throw e
  let some inst := hItems top.generates
    | throw "no child instance in source-shaped hierarchy"
  let some child := lib.find? (·.name == inst.module)
    | throw s!"module '{inst.module}' is not in the envelope library"
  let given ← inst.given env child
  let (child', _) ← child.atPoint given
  let pfx ← inst.prefix env
  pure (child', inst, pfx)

/-- Build a one-child source-shaped memory design. The child may contain the
parameter-sized unpacked storage; parent and child parameter names remain
source-shaped, so `PDesign.instantiateCoreMem` binds dimensions at the top point. -/
def CoreMemDesign.ofHierarchy (top : PDesign) (lib : List PDesign) (args : List Int) :
    Res CoreMemDesign :=
  match childDesign top lib args with
  | .error e => .unsupported s!"Instance:memory: {e}"
  | .ok (child, inst, pfx) =>
    let childDecls := child.decls.map fun pd => { pd with
      name := pfx ++ pd.name
      isInput := false
      isOutput := false }
    let clockMap := inst.conns.filterMap fun c =>
      match c with | .input port (some (.ident actual)) _ => some (port, actual) | _ => none
    let childPs := child.processes.map (hProcess pfx clockMap)
    let inputPs := inst.conns.filterMap fun c =>
      match c with
      | .input port (some actual) _ => some (.assign (pfx ++ port) actual)
      | _ => none
    let outputPs := inst.conns.filterMap fun c =>
      match c with
      | .output port (some (.ident target)) => some (.assign target (.ident (pfx ++ port)))
      | _ => none
    let merged := { top with
      decls := top.decls ++ childDecls
      processes := top.processes ++ inputPs ++ childPs ++ outputPs
      generates := []
      others := top.others ++ child.others }
    match PDesign.instantiateCoreMem merged args with
    | .ok d => .ok d
    | .timeout => .timeout
    | .unsupported e => .unsupported e


end LeanModels.Sv.Kernel
