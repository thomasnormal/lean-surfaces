// A parameter-wide signed signal compared with a sized signed literal: at `W = 8` the literal is as wide as `x`, at
// `W < 8` the signal is the narrower operand and is sign-extended (IEEE 1800-2023 §11.8.2) where the envelope, elaborated
// at the default, has no marker for it.
module sg_cmp_sext_param #(parameter int W = 8) (
    input  logic signed [W-1:0] x,
    output logic                y
);
    assign y = x >= 8'sd0;
endmodule
