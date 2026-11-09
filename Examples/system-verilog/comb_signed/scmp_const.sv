// Signed comparisons with a constant (IEEE 1800-2023 §11.4.4, §11.8.1): the comparison is signed when both operands are,
// and its operands are compared at the wider of their widths as two's-complement integers.
// * an 8-bit signed signal against sized signed literals of its width, the constant on either side (a negative one
//   written as its bits: 8'sb1111_1101 is -3);
// * a 32-bit signed signal against unsized constants (32-bit signed integers), on either side.
module scmp_const (
    input  logic signed [7:0]  x,
    input  logic signed [31:0] z,
    output logic               x_ge0,
    output logic               x_le0r,
    output logic               x_ltm3,
    output logic               x_gt100r,
    output logic               z_ge0,
    output logic               z_lt5,
    output logic               z_le0r
);
    assign x_ge0    = x >= 8'sd0;
    assign x_le0r   = 8'sd0 <= x;
    assign x_ltm3   = x < 8'sb1111_1101;
    assign x_gt100r = 8'sd100 > x;
    assign z_ge0    = z >= 0;
    assign z_lt5    = z < 5;
    assign z_le0r   = 0 <= z;
endmodule
