// Still outside: an arithmetic shift `>>>` in a self-determined position (the operand of a reduction) inside the left
// operand of a shift. Self-determined operands there are read as the v1 fragment, which has no shift.
module sh_self_asr #(parameter int W = 8) (
    input  logic signed [W-1:0] a,
    output logic        [W-1:0] y
);
    assign y = (|(a >>> 2)) << 1;
endmodule
