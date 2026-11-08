import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2

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
      .ok ({ name := i.name, module := i.module, child := child', args := childArgs,
             ports := i.conns } :: tail)
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

#guard match hierarchyInsts {} [] [] with
  | .ok [] => true
  | _ => false

end LeanModels.Sv

