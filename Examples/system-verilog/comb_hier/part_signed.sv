// A part select of a signed input passed through a module port (the clean-room repro, verbatim below this header).
module signed_select_leaf (
    input logic [3:0] a,
    output logic y
);
    assign y = a[0];
endmodule

module signed_select_shift (
    input logic signed [7:0] x,
    output logic y
);
    signed_select_leaf leaf(.a(x[3:0]), .y(y));
endmodule
