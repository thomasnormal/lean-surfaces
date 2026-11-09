// Shifts of signed operands: the left operand of a signed shift as an operation (`instDivOperand2` lowers it with every
// leaf sign-extended to the operation width), an arithmetic shift into a target wider than its operand (the operand is
// sign-extended before the shift, IEEE 1800-2023 §11.6.1, §11.8.2), and a part select of a signed signal (an unsigned
// value, §11.8.1) as the left operand of an unsigned shift.
module shift_signed #(parameter int W = 8) (
    input  logic signed [W-1:0] a,
    input  logic signed [W-1:0] b,
    input  logic        [2:0]   s,
    output logic signed [W-1:0] y_sum,
    output logic signed [W:0]   y_wide,
    output logic        [W-2:0] y_sel
);
    assign y_sum  = (a + b) >>> 1;
    assign y_wide = a >>> s;
    assign y_sel  = a[W-1:1] >> s;
endmodule
