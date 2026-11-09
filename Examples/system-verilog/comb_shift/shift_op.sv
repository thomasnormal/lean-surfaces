// A shift whose left operand is an operation (the downstream clean-room repro `shift_operand_tactic.sv`, as reported).
module shift_operand_window #(parameter int W = 8) (
    input logic [W-1:0] a,
    input logic [W-1:0] b,
    output logic [W-1:0] y
);
    logic [W-1:0] passthrough;
    assign passthrough = a;
    assign y = (a + b) << 2;
endmodule
