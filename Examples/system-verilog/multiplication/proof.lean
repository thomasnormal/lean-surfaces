import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.multiplication.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

load_design_sv2 multiplier from
  "Examples/system-verilog/multiplication/multiplier.sv.json"

def sourceProduct : PExpr :=
  match multiplier.pdesign.processes with
  | [.assign "product" value] => value
  | _ => .unsupported "Multiplier:shape" "continuous assignment changed"

theorem source_product :
    sourceProduct = .binary .mul (.ident "left") (.ident "right") := rfl

def productExpr (width : Nat) : Expr :=
  instExpr { widths := [("left", width), ("right", width)] }
    (some width) sourceProduct

theorem product_instantiation (width : Nat) :
    productExpr width = .binary .mul (.ident "left") (.ident "right") := by
  change instExpr { widths := [("left", width), ("right", width)] }
    (some width) sourceProduct = _
  rw [source_product]
  simp [instExpr, evalInt, selfWidth, List.lookup]
  rfl

def runProduct {width : Nat} (left right : BitVec width) : Res LVec :=
  evalExpr 8 [("left", .ofBitVec left), ("right", .ofBitVec right)]
    (productExpr width)

#guard runProduct (13 : BitVec 8) (23 : BitVec 8) == .ok (.ofBitVec (43 : BitVec 8))
#guard runProduct (13 : BitVec 16) (23 : BitVec 16) == .ok (.ofBitVec (299 : BitVec 16))

theorem multiplication_modular {width : Nat} (left right : BitVec width) :
    runProduct left right = .ok (.ofBitVec (left * right)) := by
  simp [runProduct, product_instantiation, evalExpr, evalBinOp,
    readSignal, SvState.lookup, LVec.mul_ofBitVec]

#print axioms multiplication_modular

def runtimeEnv : IEnv := { widths := [("left", 4), ("right", 8)] }

#guard instExpr {} (some 8) (.binary .mul (.int 13) (.int 23)) ==
  .lit (.ofInt 8 299)
#guard instExpr2 {} [] (some 16) (.binary .mul (.int 13) (.int 23)) ==
  .lit (.ofInt 16 299)
#guard (match evalInt {} (.binary (.m0 .mul) (.int 13) (.int 23)) with
  | .ok value => value == 299
  | .error _ => false)
#guard (multiplier 8).processes[0]? ==
  some (Process.assign "product" (productExpr 8))
#guard (match (multiplier.sem 16).processes[0]? with
  | some (Process2.assign (.ident "product") value) =>
      value == .binary .mul (.ident "left") (.ident "right")
  | _ => false)
#guard instExpr2 runtimeEnv [] (some 16) sourceProduct ==
  .binary .mul (.resize 16 (.ident "left")) (.resize 16 (.ident "right"))
#guard instExpr2 runtimeEnv [] none sourceProduct ==
  .binary .mul (.resize 8 (.ident "left")) (.ident "right")
-- A context narrower than the operands: the product runs at the operands'
-- width and is truncated to the context (an x bit above the context
-- collapses it, IEEE 1800-2023 §11.4.3).
#guard instExpr2 runtimeEnv [] (some 2) sourceProduct ==
  .resize 2 (.binary .mul (.resize 8 (.ident "left")) (.ident "right"))
#guard instExpr2 runtimeEnv [] (some 2)
  (.binary (.m0 .mul) (.ident "left") (.ident "right")) ==
  .resize 2 (.binary .mul (.resize 8 (.ident "left")) (.ident "right"))
#guard evalExpr2 16 [("left", .lit "1101"), ("right", .ofNat 8 23)]
  (instExpr2 runtimeEnv [] (some 16) sourceProduct) == .ok (.ofNat 16 299)
#guard evalBinOp .mul (.ofNat 4 0) (.lit "0x10") == .xVec 4
#guard evalBinOp .mul (.lit "01z0") (.ofNat 4 3) == .xVec 4

#eval do
  let text ← IO.FS.readFile
    "Examples/system-verilog/multiplication/runtime_contexts.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "real multiplication fixture failed to load")
  let some (SProc.initial (.block statements)) := design.procs[0]?
    | throw (IO.userError "real multiplication process shape changed")
  unless statements[2]? == some (SStmt.m0 (.blockingAssign "product" (productExpr 8))) do
    throw (IO.userError "real multiplication assignment changed")
  unless runSelfCheck design 4096 == Res.ok ["PASS"] do
    throw (IO.userError "real multiplication fixture did not print PASS")

end Examples.systemVerilog.multiplication.proof
