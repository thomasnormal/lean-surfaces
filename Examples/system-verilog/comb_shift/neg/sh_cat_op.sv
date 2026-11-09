// Still outside: an OPERATION as a concatenation part inside the left operand of a shift (the arithmetic shift `a >>> 1`
// of a signed `a`). A part is read as a sized literal, one access or a replication.
module sh_cat_op #(parameter int W = 8) (
    input  logic signed [W-1:0]   a,
    input  logic        [W-1:0]   b,
    output logic        [W+W-1:0] y
);
    assign y = {a >>> 1, b} << 1;
endmodule
