// Refused construct: an FF-only cycle proof applied to a valid/ready register chain with comb outputs.
// Refused by: SeqProfile.ffOnlyProfileB.
// Exact message: ffOnlyProfileB = false (the design is admitted by the mixed sequential profile).
module valid_chain_profile #(parameter integer W = 8) (
    input logic clk,
    input logic rst,
    input logic valid_i,
    input logic ready_i,
    input logic [W-1:0] data_i,
    output logic valid_o,
    output logic [W-1:0] data_o
);
    logic valid_q;
    logic [W-1:0] data_q;
    always_ff @(posedge clk) begin
        if (rst) begin valid_q <= 1'b0; data_q <= '0; end
        else if (ready_i) begin valid_q <= valid_i; data_q <= data_i; end
    end
    assign valid_o = valid_q;
    assign data_o = data_q;
endmodule
