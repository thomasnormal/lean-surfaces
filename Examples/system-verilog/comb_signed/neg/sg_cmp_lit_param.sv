// Still outside: a signed comparison of a signed signal of a PARAMETER width with a sized literal. At the default
// `W = 8` the widths agree; at another width one operand is extended (IEEE 1800-2023 §11.8.2), and the semantics extends
// a sized literal with zeros, so the fragment reads the literal only against a signal of a constant width equal to it.
module sg_cmp_lit_param #(parameter int W = 8) (
    input  logic signed [W-1:0] x,
    output logic                y
);
    assign y = x >= 8'sd0;
endmodule
