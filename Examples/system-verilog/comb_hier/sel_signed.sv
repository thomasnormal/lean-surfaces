// A bit select of a signed input passed through a module port (the clean-room repro, verbatim below this header).
module signed_bit_select_leaf (
    input logic a,
    output logic y
);
    assign y = a;
endmodule

module signed_bit_select (
    input logic signed [7:0] x,
    output logic y
);
    signed_bit_select_leaf leaf(.a(x[0]), .y(y));
endmodule
