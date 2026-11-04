// Round 6 folds (round 5 FOLDS verifier major 3, repro `vs_up`): an UNTYPED
// PARAMETER whose default is built with `+`: 9 bits in Icarus 12.0, 8 in
// slang and the Yosys 0.53 netlist at the default point (o1: 130 against 2
// at SB = 5), refused there (Constant:untyped-width). Overridden by an
// integer it is an `int` in every tool, and runs.
module fold_uwidp #(parameter int N = 8, parameter logic [N-1:0] SB = 8'd5,
                    parameter Y = SB + 1'b1) (
  input  logic [7:0] a,
  output logic [7:0] o1,
  output logic o2);
  assign o1 = (Y + a) >> 1;
  assign o2 = (Y + a) < 8'd10;
endmodule
