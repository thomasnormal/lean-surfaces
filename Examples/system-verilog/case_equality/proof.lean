import LeanModels.Sv.Json
import LeanModels.Sv.Semantics

namespace Examples.systemVerilog.caseEquality.proof

open LeanModels.Sv

set_option autoImplicit false

theorem exact_case_equality :
    evalBinOp .caseEq (.lit "1x") (.lit "1x") = .lit "1" := rfl

theorem distinct_unknown_states :
    evalBinOp .caseEq (.lit "1x") (.lit "1z") = .lit "0" := rfl

theorem case_inequality :
    evalBinOp .caseNe (.lit "z") (.lit "x") = .lit "1" := rfl

def caseEnvelopeText : String := r#"{
  "schema_version": "sv-0.1",
  "language": "systemverilog",
  "source_file": "case_equality.sv",
  "source_sha256": "",
  "design": {
    "kind": "Design",
    "name": "case_equality",
    "decls": [
      {"name": "clk", "width": 1, "is_input": true},
      {"name": "value", "width": 2, "is_input": true},
      {"name": "eq", "width": 1, "is_output": true},
      {"name": "neq", "width": 1, "is_output": true}
    ],
    "processes": [{
      "kind": "AlwaysFF", "clock": "clk",
      "body": {"kind": "Block", "stmts": [
        {"kind": "BlockingAssign", "target": "eq",
         "value": {"kind": "Binary", "op": "===",
                   "left": {"kind": "Ident", "name": "value"},
                   "right": {"kind": "Literal", "width": 2, "value": "1x"}}},
        {"kind": "BlockingAssign", "target": "neq",
         "value": {"kind": "Binary", "op": "!==",
                   "left": {"kind": "Ident", "name": "value"},
                   "right": {"kind": "Literal", "width": 2, "value": "1x"}}}
      ]}
    }]
  }
}"#

def caseEqualityReceipt : IO Unit := do
  let design ← match loadDesignString caseEnvelopeText with
    | .ok design => pure design
    | .error message => throw (IO.userError message)
  let stimulus := [
    [("clk", LVec.ofNat 1 0), ("value", LVec.lit "1x")],
    [("clk", LVec.ofNat 1 0), ("value", LVec.lit "1z")],
    [("clk", LVec.ofNat 1 0), ("value", LVec.lit "10")]]
  let expectedEq := ["1", "0", "0"]
  let expectedNeq := ["0", "1", "1"]
  let .ok trace := run design σ_src 128 stimulus
    | throw (IO.userError "case-equality fixture did not run")
  unless trace.map (SvState.showSignal · "eq") == expectedEq do
    throw (IO.userError "case-equality equality trace disagrees")
  unless trace.map (SvState.showSignal · "neq") == expectedNeq do
    throw (IO.userError "case-equality inequality trace disagrees")

#eval caseEqualityReceipt

end Examples.systemVerilog.caseEquality.proof
