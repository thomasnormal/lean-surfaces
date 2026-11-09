// Still outside: `>>>` inside the left operand of an unsigned shift. `a` is signed, but the sum with the unsigned `b` is
// unsigned, so slang converts `a` to the unsigned context and the inner shift is `>>>` of an UNSIGNED operand (a logical
// shift), which the fragment does not read yet.
module sh_nested_signed #(parameter int W = 8) (
    input  logic signed [W-1:0] a,
    input  logic        [W-1:0] b,
    output logic        [W-1:0] y
);
    assign y = ((a >>> 1) + b) << 1;
endmodule
