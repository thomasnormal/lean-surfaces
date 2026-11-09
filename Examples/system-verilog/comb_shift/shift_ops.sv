// Shifts whose left operand is an operation of the fragment. The left operand of a shift is context-determined
// (IEEE 1800-2023 §11.6.1): it is computed at the width of the context, its operands extended first, so the carry of
// `a + b` survives into the wider target `c`.
module shift_ops #(parameter int W = 8) (
    input  logic [W-1:0] a,
    input  logic [W-1:0] b,
    input  logic [2:0]   s,
    output logic [W:0]   c,
    output logic [W-1:0] x,
    output logic [W-1:0] m
);
    assign c = (a + b) << 1;
    assign x = (a ^ b) >> s;
    assign m = (a & ~b) << s;
endmodule
