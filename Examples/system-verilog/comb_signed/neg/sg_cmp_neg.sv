// Still outside: a signed comparison with a NEGATED constant (`x < -5`): unary minus is outside the fragment.
module sg_cmp_neg (
    input  logic signed [31:0] z,
    output logic               y
);
    assign y = z < -5;
endmodule
