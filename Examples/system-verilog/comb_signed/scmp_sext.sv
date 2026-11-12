// Signed comparisons whose narrower operand is sign-extended (IEEE 1800-2023 §11.8.2, §11.6.1): the envelope marks the
// extension `SignedResize`, and the loader reads a signed literal under a marker of its own.
// * `x >= 8'sd0`: the literal is as wide as `x` (only the loader's marker);
// * `x < 16'sd5`: both operands extended to 16 bits;
// * `w < 8'sb1111_1101`: the 8-bit literal -3 extended to the 16 bits of `w`;
// * `0 < x`: `x` extended to the 32 bits of the unsized constant, the constant on the left;
// * `x <= w`: `x` extended to the 16 bits of `w`.
module scmp_sext (
    input  logic signed [7:0]  x,
    input  logic signed [15:0] w,
    output logic               x_ge0,
    output logic               x_lt5,
    output logic               w_ltm3,
    output logic               x_gt0r,
    output logic               x_le_w
);
    assign x_ge0  = x >= 8'sd0;
    assign x_lt5  = x < 16'sd5;
    assign w_ltm3 = w < 8'sb1111_1101;
    assign x_gt0r = 0 < x;
    assign x_le_w = x <= w;
endmodule
