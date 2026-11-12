// A whole signed input connected to a wider port: the connection sign-extends the actual (IEEE 1800-2023 §23.3.3,
// §10.7, §11.8.2), a width-changing connection the hierarchy summary does not read.
module wide_leaf (
    input logic [7:0] a,
    output logic [7:0] y
);
    assign y = a;
endmodule

module signed_port_wide (
    input logic signed [3:0] x,
    output logic [7:0] y
);
    wide_leaf leaf(.a(x), .y(y));
endmodule
