import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2
import LeanModels.Sv.Kernel.RunEArray

/-!
# Source-shaped hierarchy nodes

`Hier2` is the established flattened F3 route.  This adapter is the first
source-shaped composition handle: an instance remains a node carrying its
child definition, parameter point, and §23.3.3 port connections.  The core
`Design2` contains only the parent's own declarations and processes; no child
signal or process is hoisted into it.

The executor deliberately delegates instance-bearing nodes to the future
composition route with a named refusal.  Instance-free nodes use the ordinary
`run2` cycle semantics, so this file adds no second scheduler and no new
`Stmt2` constructor.
-/

namespace LeanModels.Sv

structure HierInstance2 where
  name : String
  module : String
  child : PDesign
  args : List Int
  ports : List PConn
deriving Repr, Inhabited

structure HierNode2 where
  core : Design2
  instances : List HierInstance2
deriving Repr, Inhabited

/-! Instance connection bounds are elaborated in the parent parameter
environment before the child is run.  Keeping the connection node itself
source-shaped lets the composition route handle direct identifiers and
constant packed slices without flattening either module. -/

def specializeBound (env : IEnv) (e : PExpr) : PExpr :=
  match evalInt env e with
  | .ok x => .int x
  | .error _ => e

def specializeConnExpr (env : IEnv) : PExpr → Res PExpr
  | .arrayPart n is mode a b =>
      .ok (.arrayPart n is mode (specializeBound env a) (specializeBound env b))
  | e => .ok e

def specializeConnLhs (env : IEnv) : PLhs → Res PLhs
  | .arrayPart n is mode a b => do
      .ok (.arrayPart n is mode (specializeBound env a) (specializeBound env b))
  | l => .ok l

def specializeConn (env : IEnv) : PConn → Res PConn
  | .input port (some e) net => do
      .ok (.input port (some (← specializeConnExpr env e)) net)
  | .output port (some l) => do
      .ok (.output port (some (← specializeConnLhs env l)))
  | c => .ok c

def hierarchyInsts (env : IEnv) (lib : List PDesign) : List GenItem → Res (List HierInstance2)
  | [] => .ok []
  | .inst i :: rest => do
      let some child := lib.find? (·.name == i.module)
        | .unsupported s!"instance '{i.name}': module '{i.module}' is not in the envelope library"
      let given ←
        match i.given env child with
        | .ok given => .ok given
        | .error msg => .unsupported s!"instance '{i.name}' of '{child.name}': {msg}"
      let (child', childArgs) ←
        match child.atPoint given with
        | .ok result => .ok result
        | .error msg => .unsupported s!"instance '{i.name}' of '{child.name}': {msg}"
      let tail ← hierarchyInsts env lib rest
      let ports ← i.conns.mapM (specializeConn env)
      .ok ({ name := i.name, module := i.module, child := child', args := childArgs,
             ports := ports } :: tail)
  | _ :: rest => hierarchyInsts env lib rest

def dropInstanceRefusals : List Process2 → List Process2
  | [] => []
  | .unsupported "Instance" _ :: rest => dropInstanceRefusals rest
  | p :: rest => p :: dropInstanceRefusals rest

/-- Instantiate only the parent's own semantic core and retain each direct
instance as a `HierInstance2` node.  Child definitions remain source-shaped
`PDesign`s; this is intentionally not `PDesign.instantiateH`. -/
def PDesign.instantiateNode2 (d : PDesign) (lib : List PDesign) (args : List Int)
    (iterFuel : Nat := 4096) : Res HierNode2 := do
  let env ← d.paramEnv2 args
  let core ← d.instantiate2 args iterFuel
  let instances ← hierarchyInsts env lib d.generates
  .ok { core := { core with processes := (dropInstanceRefusals core.processes.toList).toArray },
        instances := instances }

def runHier2 (h : HierNode2) (σ : ScheduleOracle) (fuel : Nat)
    (stim : List SvState) : Res (List SvState) :=
  if h.instances.isEmpty then
    run2 h.core σ fuel stim
  else
    .unsupported "Instance:hierarchy: source-shaped instance nodes require the E composition route; no flattening rewrite is applied"

/-! ## The first E composition route

This is deliberately source-shaped and narrow: one direct child, direct
identifier port connections, and assign/always_comb child bodies.  The parent
state supplies child inputs; the child E run supplies the connected outputs.
No child declaration or process is flattened into the parent.  Other port
expressions, multiple children, and nested hierarchy remain loud. -/

def directInput (parent : SvState) : PConn → Res (Option (String × LVec))
  | .input port (some (.ident actual)) _ =>
      match SvState.lookup parent actual with
      | some v => .ok (some (port, v))
      | none => .unsupported "Instance:hierarchy: input actual is not in the parent state"
  | .input port (some (.arrayPart actual [] .range (.int hi) (.int lo))) _ =>
      match SvState.lookup parent actual with
      | some v =>
          let off := lo.toNat
          let width := (hi - lo + 1).toNat
          .ok (some (port, ⟨v.bits.extract off width⟩))
      | none => .unsupported "Instance:hierarchy: input actual is not in the parent state"
  | .input port none _ => .ok none
  | .input _ _ _ => .unsupported "Instance:hierarchy: non-identifier input connection"
  | .output _ _ | .unsupported _ _ _ => .ok none

def directOutput : PConn → Option (String × String)
  | .output port (some (.ident actual)) => some (port, actual)
  | _ => none

def setSlice (st : SvState) (name : String) (lo width : Nat) (value : LVec) : SvState :=
  match SvState.lookup st name with
  | none => st
  | some old =>
      Id.run do
        let mut bits := old.bits
        for j in [0:width] do
          if hdst : lo + j < bits.size then
            if hsrc : j < value.bits.size then
              bits := bits.set! (lo + j) (value.bits[j]'hsrc)
        return SvState.set st name ⟨bits⟩

def projectOutput (parent : SvState) (child : SvState) : PConn → SvState
  | .output port (some (.ident actual)) =>
      match SvState.lookup child port with
      | some v => SvState.set parent actual v
      | none => parent
  | .output port (some (.arrayPart actual [] .range (.int hi) (.int lo))) =>
      match SvState.lookup child port with
      | some v => setSlice parent actual lo.toNat (hi - lo + 1).toNat v
      | none => parent
  | _ => parent

def childState (parent : SvState) (decls : Array Decl) (ports : List PConn) : Res SvState := do
  let inputs ← ports.mapM (directInput parent)
  let mut st : SvState := []
  for dc in decls.toList do
    if dc.isInput then
      match inputs.find? (fun x => x.map (·.1) == some dc.name) with
      | some (some (_, v)) => st := st ++ [(dc.name, v)]
      | _ => st := st ++ [(dc.name, LVec.xVec dc.width)]
    else st := st ++ [(dc.name, LVec.xVec dc.width)]
  return st

def projectOutputs (parent : SvState) (child : SvState) (ports : List PConn) : SvState :=
  ports.foldl (fun st c => projectOutput st child c) parent

def runChildE0 (parent : SvState) (fuel : Nat) (σ : ScheduleOracle)
    (i : HierInstance2) : Res SvState := do
  let childD ← i.child.instantiate2 i.args
  let cs ← childState parent childD.decls i.ports
  match Kernel.runE0Array (Kernel.Elab.ofDesign2 childD) σ fuel [cs] with
  | .ok [row] =>
      .ok (projectOutputs parent
        (Kernel.Elab.view (Kernel.Elab.ofDesign2 childD) row.2.store) i.ports)
  | .ok _ => .unsupported "Instance:hierarchy: child E route returned no row"
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

def runChildrenE0 (parent : SvState) (fuel : Nat) (σ : ScheduleOracle) :
    List HierInstance2 → Res SvState
  | [] => .ok parent
  | i :: rest => do
      let after ← runChildE0 parent fuel σ i
      runChildrenE0 after fuel σ rest

def initParent (decls : Array Decl) (input : SvState) : SvState :=
  decls.toList.map (fun dc =>
    (dc.name, (SvState.lookup input dc.name).getD (LVec.xVec dc.width)))

def runHierE0 (h : HierNode2) (σ : ScheduleOracle) (fuel : Nat)
    (stim : List SvState) : Res (List SvState) :=
  match h.instances with
  | _ :: _ => stim.mapM (fun parent => runChildrenE0 (initParent h.core.decls parent) fuel σ h.instances)
  | [] =>
      match Kernel.runE0Array (Kernel.Elab.ofDesign2 h.core) σ fuel stim with
      | .ok rows => .ok (rows.map fun r => Kernel.Elab.view (Kernel.Elab.ofDesign2 h.core) r.2.store)
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

#guard match hierarchyInsts {} [] [] with
  | .ok [] => true
  | _ => false

end LeanModels.Sv

