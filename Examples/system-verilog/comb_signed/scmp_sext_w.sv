// A signed comparison of a parameter-wide signed signal with an unsized constant: `x` is sign-extended to the 32 bits of
// the constant where it is narrower, and the constant is materialized at the width of `x` where `x` is wider (IEEE
// 1800-2023 §11.8.2): `y` is `x >= 0` at every width.
module scmp_sext_w #(parameter int W = 8) (
    input  logic signed [W-1:0] x,
    output logic                y
);
    assign y = x >= 0;
endmodule
