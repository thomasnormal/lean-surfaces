// Still outside: the arithmetic shift `>>>` of a signed OPERATION (the left operand of a signed shift is read as a
// signal access, a sized literal or a constant).
module sh_signed_op #(parameter int W = 8) (
    input  logic signed [W-1:0] a,
    input  logic signed [W-1:0] b,
    output logic signed [W-1:0] y
);
    assign y = (a + b) >>> 1;
endmodule
