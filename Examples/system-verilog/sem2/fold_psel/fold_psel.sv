// Round 3 folds, item 2: literal-label selects of a LOCALPARAM whose range
// depends on a parameter. The labels are offsets from bit 0 only while the
// range is [N-1:0] with N >= 1; at N = 1 label 1 is out of range (Icarus
// and Yosys read x), at N = 0 the range is the ascending [-1:0].
module fold_psel #(parameter int N = 4) (
  input  logic       a,
  output logic       o1,
  output logic [1:0] o2,
  output logic       o3
);
  localparam logic [N-1:0] P = 3;
  localparam logic [N-1:0] Q = 2;
  assign o1 = P[1];
  assign o2 = Q[0 +: 2];
  if (Q[1]) begin : g1
    assign o3 = 1'b1;
  end else begin : g0
    assign o3 = 1'b0;
  end
endmodule
