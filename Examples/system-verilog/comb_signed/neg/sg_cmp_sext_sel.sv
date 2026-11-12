// A sign-extended operand that is not a whole signed signal or a sized literal: `$signed(x[3:0])` extended to the 32 bits
// of the unsized constant (IEEE 1800-2023 §11.8.2).
module sg_cmp_sext_sel (
    input  logic [7:0] x,
    output logic       y
);
    assign y = $signed(x[3:0]) >= 0;
endmodule
