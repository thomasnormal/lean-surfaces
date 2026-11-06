import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.signed_index.proof

open LeanModels.Sv

load_design_sv2 a1signed from
  "Examples/system-verilog/sem2/signed_index/a1/a1_signed_idx.sv.json"
load_design_sv2 c1signed from
  "Examples/system-verilog/sem2/signed_index/c1/c1_signed_wridx.sv.json"

private def a1run := run2 (a1signed.sem 8) σ_src 256 [
  [("clk", .ofNat 1 0), ("rst", .ofNat 1 1), ("en", .ofNat 1 0),
   ("q", .xVec 8), ("a", .xVec 4), ("i", .xVec 2)],
  [("clk", .ofNat 1 1), ("rst", .ofNat 1 0), ("en", .ofNat 1 0),
   ("q", .xVec 8), ("a", .xVec 4), ("i", .xVec 2)],
  [("clk", .ofNat 1 0), ("rst", .ofNat 1 0), ("en", .ofNat 1 0),
   ("q", .xVec 8), ("a", .xVec 4), ("i", .xVec 2)] ]
#eval a1run

#guard match a1run with | .ok _ => true | _ => false

private def c1run := run2 (c1signed.sem 8) σ_src 256 [
  [("clk", .ofNat 1 0), ("rst", .ofNat 1 1), ("en", .ofNat 1 0),
   ("q", .xVec 8), ("i", .xVec 2)],
  [("clk", .ofNat 1 1), ("rst", .ofNat 1 0), ("en", .ofNat 1 0),
   ("q", .xVec 8), ("i", .xVec 2)] ]
#eval c1run

#guard match c1run with | .ok _ => true | _ => false

/- The source-shaped envelopes above exercise the parser and lowering.  These
  direct semantic guards pin the distinction that motivated the packet:
  `2'b10` is -2 when it is the signed declaration index, so a read is all-x
  and a write is a no-op; the old unsigned path would read/write element 2. -/
private def signedReadState : SvState :=
  [("a", .ofNat 4 1), ("i", .ofNat 2 2), ("q", .xVec 4)]

#guard evalExpr2 32 signedReadState
    (.index (.ident "a") (.resizeSigned 2 (.ident "i")) 1)
    == .ok (.xVec 1)

#guard resolveLhs2 32 signedReadState
    (.index "q" (.resizeSigned 2 (.ident "i")) 1)
    == .ok ("q", none)

#guard commitNba2 signedReadState
    (match execStmt2 32 signedReadState []
        (.nbaAssign (.index "q" (.resizeSigned 2 (.ident "i")) 1)
          (.lit (.ofNat 1 1))) with
     | .ok (_, nba) => nba
     | _ => [])
    == signedReadState

end Examples.«system-verilog».sem2.signed_index.proof
