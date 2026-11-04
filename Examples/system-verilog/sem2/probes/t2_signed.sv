// Phase-2 probe: $signed casts and signed vs unsigned comparison;
// same-width casts are bit identities under - and subtraction.
module t2_signed (
    input  logic [7:0] a, b,
    output logic slt_o, ult_o, sge_o,
    output logic [7:0] diff_o, neg_o
);
  assign slt_o  = $signed(a) < $signed(b);
  assign ult_o  = a < b;
  assign sge_o  = $signed(a) >= $signed(b);
  assign diff_o = a - $signed(b);
  assign neg_o  = -$signed(a);
endmodule
