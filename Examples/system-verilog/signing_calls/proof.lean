import LeanModels.Sv.SelfCheck
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.signingCalls.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

def signingBody : SStmt :=
  .block #[
    .m0 (.blockingAssign "same_signed" (.ident "value")),
    .m0 (.blockingAssign "same_unsigned" (.ident "value")),
    .assign false "wide_signed" (.signedResize 8 (.m0 (.ident "value"))),
    .assign false "wide_unsigned" (.resize 8 (.m0 (.ident "value")))]

def runSigning (value : LVec) : Res (SvState × NbaQueue × Out) :=
  execSStmt 64 [ ("value", value), ("same_signed", .xVec 4),
    ("same_unsigned", .xVec 4), ("wide_signed", .xVec 8),
    ("wide_unsigned", .xVec 8) ] [] {} signingBody

#guard runSigning (.lit "1001") == .ok
  ([ ("value", .lit "1001"), ("same_signed", .lit "1001"),
    ("same_unsigned", .lit "1001"), ("wide_signed", .lit "11111001"),
    ("wide_unsigned", .lit "00001001") ], [], {})

#guard runSigning (.lit "x01z") == .ok
  ([ ("value", .lit "x01z"), ("same_signed", .lit "x01z"),
    ("same_unsigned", .lit "x01z"), ("wide_signed", .lit "xxxxx01z"),
    ("wide_unsigned", .lit "0000x01z") ], [], {})

theorem signing_assignment_contexts (value : LVec) :
    runSigning value = .ok
      ([ ("value", value), ("same_signed", value), ("same_unsigned", value),
        ("wide_signed", value.resizeSigned 8),
        ("wide_unsigned", resizeV 8 value) ], [], {}) := by
  simp [runSigning, signingBody, execSStmt, execSStmts, execStmt, evalSExpr,
    evalExpr, readSignal, SvState.lookup, SvState.set, Bind.bind, Pure.pure]

#print axioms signing_assignment_contexts

#eval do
  let text ← IO.FS.readFile
    "Examples/system-verilog/signing_calls/assignment_contexts.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "real signing-call fixture failed to load")
  let some (SProc.initial (.block statements)) := design.procs[0]?
    | throw (IO.userError "real signing-call process shape changed")
  let .block expected := signingBody
    | throw (IO.userError "signing-call certificate shape changed")
  for index in [0, 1, 2, 3] do
    unless statements[index + 1]? == expected[index]? do
      throw (IO.userError s!"signing-call statement {index} changed")
  unless runSelfCheck design 4096 == Res.ok ["PASS"] do
    throw (IO.userError "real signing-call fixture did not print PASS")

end Examples.systemVerilog.signingCalls.proof
