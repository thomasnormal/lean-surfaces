import LeanModels.Circuit.MixedSignal
import LeanModels.Circuit.Discipline

/-!
# Verilog-AMS lowering target

This is a typed semantic IR, not a source parser. A future Verilog-AMS
frontend must project an existing, pinned third-party AST into these types.
OpenVAF remains the parser for the current Verilog-A subset; unsupported AMS
syntax must never be guessed by a handwritten fallback parser.
-/

namespace LeanModels.VerilogAMS

open LeanModels.Circuit

structure DisciplineRef where
  name : String
deriving Repr, BEq, DecidableEq, Inhabited

structure PortDecl where
  name : String
  discipline : DisciplineRef
deriving Repr, BEq, DecidableEq, Inhabited

inductive ConnectDirection
  | logicToElectrical
  | electricalToLogic
deriving Repr, BEq, DecidableEq, Inhabited

structure ConnectModule where
  name : String
  direction : ConnectDirection
  levels : LogicElectricalLevels
deriving Inhabited

inductive EventControl where
  | cross (expression : String) (direction : Int)
  | timer (first period : Rat)
  | digital (signal : String)
deriving Repr, BEq, DecidableEq, Inhabited

structure EventContribution where
  control : EventControl
  microstep : Nat
  target : String
deriving Repr, BEq, DecidableEq, Inhabited

structure Module where
  name : String
  ports : Array PortDecl
  connectModules : Array ConnectModule
  events : Array EventContribution
deriving Inhabited

end LeanModels.VerilogAMS
