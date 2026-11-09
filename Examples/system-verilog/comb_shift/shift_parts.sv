// Shifts whose left operand holds the self-determined sub-operands slang wraps in conversion markers inside a shift
// operand: a concatenation, the condition of `?:`, `!`, a reduction, a comparison with a constant, a comparison of two
// widths inside a sum, and a signed signal inside an unsigned sum.
module shift_parts #(parameter int W = 8) (
    input  logic        [W-1:0]   a,
    input  logic        [W-1:0]   b,
    input  logic                  c,
    input  logic        [2:0]     s,
    input  logic signed [W-1:0]   sa,
    output logic        [W+W-1:0] y_cat,
    output logic        [W:0]     y_one,
    output logic        [W-1:0]   y_tern,
    output logic        [W-1:0]   y_lnot,
    output logic        [W-1:0]   y_red,
    output logic        [W-1:0]   y_eqz,
    output logic        [W:0]     y_cmp,
    output logic        [W-1:0]   y_sgn
);
    assign y_cat  = {a, b} >> s;
    assign y_one  = {1'b1, a} >> 1;
    assign y_tern = (c ? a : b) << 1;
    assign y_lnot = (!a) << 2;
    assign y_red  = (&a) << s;
    assign y_eqz  = (a == 0) << 1;
    assign y_cmp  = ((a > b) + a) << s;
    assign y_sgn  = (sa + b) >> 1;
endmodule
