import LeanModels.Sv.Json
import LeanModels.Sv.Semantics

namespace Examples.systemVerilog.logicalOps.proof

open LeanModels.Sv

set_option autoImplicit false

theorem definite_false_and :
    evalBinOp .land (.lit "00") (.lit "0x") = .lit "0" := rfl

theorem ambiguous_or :
    evalBinOp .lor (.lit "0x") (.lit "00") = .lit "x" := rfl

def logicalEnvelopeText : String := r#"{
  "schema_version": "sv-0.1",
  "language": "systemverilog",
  "source_file": "logical_ops.sv",
  "source_sha256": "",
  "design": {
    "kind": "Design",
    "name": "logical_ops",
    "decls": [
      {"name": "clk", "width": 1, "is_input": true},
      {"name": "value", "width": 2, "is_input": true},
      {"name": "both", "width": 1, "is_output": true},
      {"name": "either", "width": 1, "is_output": true}
    ],
    "processes": [{
      "kind": "AlwaysFF", "clock": "clk",
      "body": {"kind": "Block", "stmts": [
        {"kind": "BlockingAssign", "target": "both",
         "value": {"kind": "Binary", "op": "&&",
                   "left": {"kind": "Ident", "name": "value"},
                   "right": {"kind": "Literal", "width": 2, "value": "01"}}},
        {"kind": "BlockingAssign", "target": "either",
         "value": {"kind": "Binary", "op": "||",
                   "left": {"kind": "Ident", "name": "value"},
                   "right": {"kind": "Literal", "width": 2, "value": "00"}}}
      ]}
    }]
  }
}"#

def logicalReceipt : IO Unit := do
  let design ← match loadDesignString logicalEnvelopeText with
    | .ok design => pure design
    | .error message => throw (IO.userError message)
  let stimulus := [
    [("clk", LVec.ofNat 1 0), ("value", LVec.lit "00")],
    [("clk", LVec.ofNat 1 0), ("value", LVec.lit "1x")],
    [("clk", LVec.ofNat 1 0), ("value", LVec.lit "xx")],
    [("clk", LVec.ofNat 1 0), ("value", LVec.lit "10")]]
  let .ok trace := run design σ_src 128 stimulus
    | throw (IO.userError "logical fixture did not run")
  unless trace.map (SvState.showSignal · "both") == ["0", "1", "x", "1"] do
    throw (IO.userError "logical conjunction trace disagrees")
  unless trace.map (SvState.showSignal · "either") == ["0", "1", "x", "1"] do
    throw (IO.userError "logical disjunction trace disagrees")

#eval logicalReceipt

end Examples.systemVerilog.logicalOps.proof
