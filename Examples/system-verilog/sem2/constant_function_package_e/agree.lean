import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.constant_function_package_e
open LeanModels.Sv
load_design_sv2 constantFunctionPackageE
  from "Examples/system-verilog/sem2/constant_function_package_e/constant_function_package_e.sv.json"
def widthAt (n : Int) : Res Nat := do
  let d ← PDesign.instantiateE2Scalar constantFunctionPackageE.pdesign [n]
  match d.decls.toList.find? (fun x => x.name == "z") with
  | some x => .ok x.width
  | none => .unsupported "missing y"
#guard constantFunctionPackageE.pdesign.functions.length == 1
#guard widthAt 1 == .ok 1
#guard widthAt 8 == .ok 3
#guard widthAt 16 == .ok 4
end Examples.«system-verilog».sem2.constant_function_package_e
