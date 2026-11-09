// Still outside: `<<<` of an unsigned operand (the same as `<<`, IEEE 1800-2023 §11.4.10). `instExpr2` lowers it to
// `BinOp.ashl`, an operator the skeleton does not build yet.
module sh_ashl #(parameter int W = 8) (
    input  logic [W-1:0] a,
    input  logic [W-1:0] b,
    output logic [W-1:0] y
);
    assign y = (a + b) <<< 1;
endmodule
