import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.division.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

load_design_sv2 divider from "Examples/system-verilog/division/divider.sv.json"
load_design_sv2 signedDivider from "Examples/system-verilog/division/signed_divider.sv.json"
load_design_sv2 contextDivider from "Examples/system-verilog/division/context_divider.sv.json"
load_design_sv2 contextDivider16 from "Examples/system-verilog/division/context_divider16.sv.json"
load_design_sv2 boundaryDivider from "Examples/system-verilog/division/boundary_divider.sv.json"

def quotientSource (design : PDesign) : PExpr :=
  match design.processes with
  | [.assign "quotient" value] => value
  | _ => .unsupported "Divider:shape" "continuous assignment changed"

theorem unsigned_source :
    quotientSource divider.pdesign =
      .binary (.m0 .div) (.ident "numerator") (.ident "denominator") := rfl

theorem signed_source :
    quotientSource signedDivider.pdesign =
      .binary (.m0 .sdiv) (.ident "numerator") (.ident "denominator") := rfl

def quotientExpr (signed : Bool) (width : Nat) : Expr :=
  instExpr { widths := [("numerator", width), ("denominator", width)] }
    (some width) (quotientSource (if signed then signedDivider.pdesign else divider.pdesign))

theorem unsigned_instantiation (width : Nat) :
    quotientExpr false width = .binary .div (.ident "numerator") (.ident "denominator") := by
  change instExpr { widths := [("numerator", width), ("denominator", width)] }
    (some width) (quotientSource divider.pdesign) = _
  rw [unsigned_source]
  simp [instExpr, instDivOperand, divOperandWidth, fitDivOperand, List.lookup]

theorem signed_instantiation (width : Nat) :
    quotientExpr true width = .binary .sdiv (.ident "numerator") (.ident "denominator") := by
  change instExpr { widths := [("numerator", width), ("denominator", width)] }
    (some width) (quotientSource signedDivider.pdesign) = _
  rw [signed_source]
  simp [instExpr, instDivOperand, divOperandWidth, fitDivOperand, List.lookup]

def runQuotient {width : Nat} (signed : Bool) (numerator denominator : BitVec width) : Res LVec :=
  evalExpr 8 [("numerator", .ofBitVec numerator), ("denominator", .ofBitVec denominator)]
    (quotientExpr signed width)

theorem unsigned_division {width : Nat} (numerator denominator : BitVec width)
    (nonzero : denominator.toNat ≠ 0) :
    runQuotient false numerator denominator = .ok (.ofBitVec (numerator / denominator)) := by
  simp [runQuotient, unsigned_instantiation, evalExpr, evalBinOp,
    readSignal, SvState.lookup, LVec.div_ofBitVec, nonzero]

theorem signed_division {width : Nat} (numerator denominator : BitVec width)
    (nonzero : denominator.toNat ≠ 0) :
    runQuotient true numerator denominator = .ok (.ofBitVec (numerator.sdiv denominator)) := by
  simp [runQuotient, signed_instantiation, evalExpr, evalBinOp,
    readSignal, SvState.lookup, LVec.sdiv_ofBitVec, nonzero]

#print axioms unsigned_division
#print axioms signed_division

def contextResults (design : Design2) : List (Res LVec) :=
  design.processes.toList.map fun process =>
    match process with
    | .assign _ expression => evalExpr2 64 [("numerator", .ofNat 8 128)] expression
    | _ => .unsupported "ContextDivider:shape continuous assignment changed"

def expectedContexts (width : Nat) : List (Res LVec) :=
  [if width == 8 then .ok (.ofNat width 64) else .ok (.ofNat width 32704),
   if width == 8 then .ok (.ofNat width 192) else .ok (.ofNat width 64),
   .ok (.ofNat width 1), .ok (.ofNat width 1), .ok (.ofNat width 1),
   .ok (.ofNat width 0), .ok (.ofNat width 0), .ok (.ofNat width 2)]

#guard contextResults (contextDivider.sem 8) == expectedContexts 8
#guard contextResults (contextDivider.sem 16) == expectedContexts 16
#guard contextResults (contextDivider16.sem 8) == expectedContexts 8
#guard contextResults (contextDivider16.sem 16) == expectedContexts 16

def boundaryResults (width : Nat) (value : Nat := 8) : List (Res LVec) :=
  (boundaryDivider.sem width).processes.toList.map fun process =>
    match process with
    | .assign _ expression => evalExpr2 64 [("value", .ofNat width value)] expression
    | _ => .unsupported "BoundaryDivider:shape continuous assignment changed"

#guard boundaryResults 4 == List.replicate 5 (.ok (.ofNat 32 0))
#guard boundaryResults 8 == List.replicate 5 (.ok (.ofNat 32 0))
#guard boundaryResults 16 == List.replicate 5 (.ok (.ofNat 32 0))
#guard boundaryResults 4 7 == [0, 8, 1, 0, 0].map (fun value => Res.ok (.ofNat 32 value))
#guard boundaryResults 8 7 == [0, 128, 1, 0, 0].map (fun value => Res.ok (.ofNat 32 value))
#guard boundaryResults 16 7 == [0, 32768, 1, 0, 0].map (fun value => Res.ok (.ofNat 32 value))
#guard boundaryResults 4 0 == [4, 68, 1, 4, 4294967292].map (fun value => Res.ok (.ofNat 32 value))
#guard boundaryResults 8 0 == [4, 1028, 1, 4, 4].map (fun value => Res.ok (.ofNat 32 value))
#guard boundaryResults 16 0 == [4, 262148, 1, 4, 4].map (fun value => Res.ok (.ofNat 32 value))

def contextM0Results (design : LeanModels.Sv.Design) : List (Res LVec) :=
  design.processes.toList.map fun process =>
    match process with
    | .assign _ expression => evalExpr 64 [("numerator", .ofNat 8 128)] expression
    | _ => .unsupported "ContextDivider:shape continuous assignment changed"

#guard (contextM0Results (contextDivider 8)).take 3 == (expectedContexts 8).take 3
#guard (contextM0Results (contextDivider 16)).take 3 == (expectedContexts 16).take 3
#guard (contextM0Results (contextDivider16 8)).take 3 == (expectedContexts 8).take 3
#guard (contextM0Results (contextDivider16 16)).take 3 == (expectedContexts 16).take 3

#guard runQuotient false (13 : BitVec 8) (5 : BitVec 8) == .ok (.ofNat 8 2)
#guard runQuotient true (-13 : BitVec 8) (5 : BitVec 8) == .ok (.ofInt 8 (-2))
#guard runQuotient true (-128 : BitVec 8) (-1 : BitVec 8) == .ok (.ofInt 8 (-128))
#guard runQuotient false (13 : BitVec 8) (0 : BitVec 8) == .ok (.xVec 8)
#guard runQuotient true (0 : BitVec 8) (0 : BitVec 8) == .ok (.xVec 8)
#guard instExpr {} (some 16) (.binary .div (.int (-13)) (.int 5)) == .lit (.ofInt 16 (-2))
#guard (match instExpr { widths := [("numerator", 8), ("denominator", 8)] }
    (some 8) (.binary .div (.ident "numerator") (.ident "denominator")) with
  | .unsupported .. => true
  | _ => false)
#guard (match instExpr2 { widths := [("numerator", 8), ("denominator", 8)] } []
    (some 8) (.binary .div (.ident "numerator") (.ident "denominator")) with
  | .unsupported .. => true
  | _ => false)

#eval do
  for fixture in ["compound", "four_state", "signed_contexts", "unsigned_contexts"] do
    let text ← IO.FS.readFile s!"harness/sv/division/{fixture}.sv.json"
    let .ok design := loadEnvelopeDesign text
      | throw (IO.userError s!"division fixture {fixture} failed to load")
    unless runSelfCheck design 4096 == Res.ok ["PASS"] do
      throw (IO.userError s!"division fixture {fixture} did not print PASS")

end Examples.systemVerilog.division.proof
