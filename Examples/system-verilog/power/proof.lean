import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.power.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

load_design_sv2 square from "Examples/system-verilog/power/square.sv.json"
load_design_sv2 power from "Examples/system-verilog/power/power.sv.json"
load_design_sv2 signedExponentPower from "Examples/system-verilog/power/signed_exponent_power.sv.json"
load_design_sv2 contextPower from "Examples/system-verilog/power/context_power.sv.json"
load_design_sv2 contextPower16 from "Examples/system-verilog/power/context_power16.sv.json"

def squareSource : PExpr :=
  match square.pdesign.processes with
  | [.assign "result" expression] => expression
  | _ => .unsupported "Square:shape" "continuous assignment changed"

theorem square_source :
    squareSource = .binary (.m0 (.pow false true)) (.ident "base") (.int 2) := rfl

def powerSource : PExpr :=
  match power.pdesign.processes with
  | [.assign "result" expression] => expression
  | _ => .unsupported "Power:shape" "continuous assignment changed"

theorem power_source :
    powerSource = .binary (.m0 (.pow false false)) (.ident "base") (.ident "exponent") := rfl

def powerExpr (width exponentWidth : Nat) : Expr :=
  instExpr { widths := [("base", width), ("exponent", exponentWidth)] }
    (some width) powerSource

theorem power_instantiation (width exponentWidth : Nat) :
    powerExpr width exponentWidth =
      .binary (.pow false false) (.ident "base") (.ident "exponent") := by
  unfold powerExpr
  rw [power_source]
  simp [instExpr, instDivOperand, divOperandWidth, fitDivOperand, List.lookup]

def runPower {width exponentWidth : Nat}
    (base : BitVec width) (exponent : BitVec exponentWidth) : Res LVec :=
  evalExpr 8 [("base", .ofBitVec base), ("exponent", .ofBitVec exponent)]
    (powerExpr width exponentWidth)

theorem unsigned_power {width exponentWidth : Nat}
    (base : BitVec width) (exponent : BitVec exponentWidth) :
    runPower base exponent = .ok (.ofNat width (base.toNat ^ exponent.toNat)) := by
  simp [runPower, power_instantiation, evalExpr, evalBinOp, readSignal, SvState.lookup,
    LVec.pow_unsigned_ofBitVec]

#print axioms unsigned_power
#print axioms LVec.powMod_eq

#guard LVec.pow false true (.ofNat 8 3) (.ofNat 4 15) == .ofNat 8 0
#guard LVec.pow false true (.ofNat 8 255) (.ofNat 4 15) == .ofNat 8 0
#guard LVec.pow false true (.ofNat 8 255) (.ofNat 4 14) == .ofNat 8 0
#guard LVec.pow true true (.ofNat 8 255) (.ofNat 4 15) == .ofNat 8 255
#guard LVec.pow true true (.ofNat 8 255) (.ofNat 4 14) == .ofNat 8 1
#guard LVec.pow true true (.ofNat 8 1) (.ofNat 4 14) == .ofNat 8 1

/-! IEEE 1800-2023 §11.4.3 Table 11-4: an integral zero base raised to a
negative signed exponent produces an all-x result. -/
#guard LVec.pow false true (.ofNat 8 0) (.ofNat 4 15) == .xVec 8
#guard LVec.pow true true (.ofNat 8 0) (.ofNat 4 15) == .xVec 8

#guard LVec.pow false true (.ofNat 32 0) (.ofNat 32 (2^32 - 1)) == .xVec 32

def contextResults (design : Design2) (exponent : Nat) : List (Res LVec) :=
  design.processes.toList.map fun process =>
    match process with
    | .assign _ expression =>
        evalExpr2 64 [("base", .ofNat 8 3), ("exponent", .ofNat 4 exponent)] expression
    | _ => .unsupported "ContextPower:shape"

def expectedContexts (width exponent : Nat) : List (Res LVec) :=
  [.ok (.ofNat width (if exponent == 15 then 0 else 243)),
   .ok (.ofNat width (if width == 8 then 0 else 16384)), .ok (.ofNat width 0)]

#guard contextResults (contextPower.sem 8) 5 == expectedContexts 8 5
#guard contextResults (contextPower.sem 16) 5 == expectedContexts 16 5
#guard contextResults (contextPower16.sem 8) 5 == expectedContexts 8 5
#guard contextResults (contextPower16.sem 16) 5 == expectedContexts 16 5
#guard contextResults (contextPower.sem 8) 15 == expectedContexts 8 15
#guard contextResults (contextPower.sem 16) 15 == expectedContexts 16 15
#guard contextResults (contextPower16.sem 8) 15 == expectedContexts 8 15
#guard contextResults (contextPower16.sem 16) 15 == expectedContexts 16 15

#eval signedExponentPower.pdesign.processes

def fixtureResults : IO Unit := do
  for fixture in ["unsigned", "signed", "zero_negative"] do
    let text ← IO.FS.readFile s!"harness/sv/power/{fixture}.sv.json"
    let .ok design := loadEnvelopeDesign text
      | throw (IO.userError s!"power fixture {fixture} failed to load")
    unless runSelfCheck design 4096 == Res.ok ["PASS"] do
      throw (IO.userError s!"power fixture {fixture} did not print PASS")

#eval fixtureResults

end Examples.systemVerilog.power.proof
