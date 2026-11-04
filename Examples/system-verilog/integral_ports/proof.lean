import LeanModels.Sv.Obs
import LeanModels.Sv.Json
import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.integralPorts.proof

open LeanModels.Sv
open Lean (Json)

set_option autoImplicit false

def portsDesign : Design :=
  { name := "integral_ports"
    decls := #[
      { name := "unsigned_bits", width := 4, isInput := true, twoState := true },
      { name := "signed_bits", width := 4, isInput := true, isSigned := true, twoState := true },
      { name := "signed_integer", width := 32, isInput := true, isSigned := true, twoState := true },
      { name := "four_state_integer", width := 32, isInput := true, isSigned := true },
      { name := "copied", width := 4, isOutput := true, twoState := true },
      { name := "value", width := 4, isOutput := true },
      { name := "negative", width := 1, isOutput := true },
      { name := "wide", width := 32, isOutput := true },
      { name := "less", width := 1, isOutput := true }]
    processes := #[
      .assign "copied" (.squash2 (.ident "unsigned_bits")),
      .assign "value" (.ident "signed_bits"),
      .assign "negative" (.binary .slt (.resizeSigned 32 (.ident "signed_bits")) (.lit (.ofNat 32 0))),
      .assign "wide" (.ident "signed_integer"),
      .assign "less" (.binary .slt (.ident "signed_integer") (.ident "four_state_integer"))] }

def fixturePort (port : Json) : Except String Decl := do
  let name ← (← port.getObjVal? "name").getStr?
  let width ← (← port.getObjVal? "width").getNat?
  let direction ← (← port.getObjVal? "dir").getStr?
  let isSigned := (port.getObjVal? "signed").toOption.bind (·.getBool?.toOption) |>.getD false
  let twoState := (port.getObjVal? "two_state").toOption.bind (·.getBool?.toOption) |>.getD false
  return { name, width, isSigned, twoState, isInput := direction == "in", isOutput := direction == "out" }

def fixtureProcess (process : Json) : Except String Process := do
  unless (← (← process.getObjVal? "kind").getStr?) == "Assign" do
    throw "expected a continuous assignment"
  let .ident target ← parseExpr (← process.getObjVal? "target")
    | throw "expected an identifier target"
  return .assign target (← parseExpr (← process.getObjVal? "value"))

def fixtureDesign (document : Json) : Except String Design := do
  let modules ← (← (← document.getObjVal? "design").getObjVal? "modules").getArr?
  let some design := modules[0]? | throw "missing module"
  unless (← (← design.getObjVal? "decls").getArr?).isEmpty &&
      (← (← design.getObjVal? "others").getArr?).isEmpty do
    throw "unexpected declaration or member"
  return { name := ← (← design.getObjVal? "name").getStr?
           decls := ← (← (← design.getObjVal? "ports").getArr?).mapM fixturePort
           processes := ← (← (← design.getObjVal? "processes").getArr?).mapM fixtureProcess }

def fixtureReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/integral_ports/integral_ports.sv.json"
  let .ok actual := Json.parse text >>= fixtureDesign
    | throw (IO.userError "integral port fixture failed to load")
  unless actual == portsDesign do
    throw (IO.userError "integral port proof AST differs from the extracted program")
  let startup ← IO.FS.readFile "Examples/system-verilog/integral_ports/startup.sv.json"
  let .ok design := SelfCheck.loadEnvelopeDesign startup
    | throw (IO.userError "integral port startup fixture failed to load")
  unless SelfCheck.runSelfCheck design 4096 == .ok ["PASS", "PASS", "PASS"] do
    throw (IO.userError "integral port startup behavior disagrees")
  let initialized ← IO.FS.readFile "Examples/system-verilog/integral_ports/initialized.sv.json"
  let .ok initializedDesign := SelfCheck.loadEnvelopeDesign initialized
    | throw (IO.userError "initialized port fixture failed to load")
  unless SelfCheck.runSelfCheck initializedDesign 4096 == .ok ["PASS"] do
    throw (IO.userError "port initializer was dropped or converted incorrectly")

#eval fixtureReceipt

theorem conversion_idempotent (value : LVec) :
    value.toTwoState.toTwoState = value.toTwoState := by
  cases value with
  | mk bits =>
    unfold LVec.toTwoState
    apply congrArg LVec.mk
    rw [Array.map_map]
    apply Array.map_congr_left
    intro bit member
    cases bit <;> rfl

theorem input_conversion_precedes_assignment (value : LVec) :
    evalExpr 4 (applyInputs portsDesign [("unsigned_bits", value)] (initState portsDesign))
      (.squash2 (.ident "unsigned_bits")) = .ok value.toTwoState := by
  simp [applyInputs, portsDesign, initState, evalExpr, readSignal,
    SvState.lookup, SvState.set, conversion_idempotent]

theorem first_assignment_copies_converted_input (value : LVec) :
    let state := applyInputs portsDesign [("unsigned_bits", value)] (initState portsDesign)
    runCombProcess 4 state portsDesign.processes[0]! =
      .ok (SvState.set state "copied" value.toTwoState) := by
  simp [runCombProcess, portsDesign, applyInputs, initState, evalExpr,
    readSignal, SvState.lookup, SvState.set, conversion_idempotent]

theorem undriven_two_state_input_starts_zero (width : Nat) :
    SelfCheck.initDecls 1
      [{ name := "signal", width, isInput := true, twoState := true }] [] =
        .ok [("signal", LVec.replicate width .l0)] := rfl

theorem undriven_four_state_input_starts_z (width : Nat) :
    SelfCheck.initDecls 1 [{ name := "signal", width, isInput := true }] [] =
      .ok [("signal", LVec.replicate width .lz)] := rfl

#print axioms conversion_idempotent
#print axioms input_conversion_precedes_assignment
#print axioms first_assignment_copies_converted_input
#print axioms undriven_two_state_input_starts_zero
#print axioms undriven_four_state_input_starts_z

end Examples.systemVerilog.integralPorts.proof
