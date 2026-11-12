// Signed reads in a parent with an instance: a whole signed input and a part select of it through ports, and the
// parent's own continuous assign over a signed input.
module mix_leaf (
    input logic [7:0] a,
    input logic [3:0] b,
    output logic [7:0] y
);
    assign y = a ^ {b, b};
endmodule

module signed_mix (
    input logic signed [7:0] x,
    input logic [7:0] w,
    output logic [7:0] y,
    output logic [7:0] z
);
    mix_leaf leaf(.a(x), .b(x[7:4]), .y(y));
    assign z = x & w;
endmodule
