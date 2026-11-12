// A signed comparison whose sign-extended operand is an operation: `a + b` is context-determined, so the sum is taken at
// the 32 bits of the unsized constant, its operands extended with their sign bits (IEEE 1800-2023 §11.6.1, §11.8.2).
module sg_cmp_sext_op (
    input  logic signed [7:0] a,
    input  logic signed [7:0] b,
    output logic              y
);
    assign y = (a + b) >= 0;
endmodule
