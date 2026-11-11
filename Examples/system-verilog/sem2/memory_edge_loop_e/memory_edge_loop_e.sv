// Refused construct: a parameter-sized unpacked memory is updated by a
// clocked for-loop.  The current E memory profile retains the source loop,
// but does not yet execute it.
// Refused by: E memory profile.
// Exact message: E memory edge loop is outside the first memory profile.
module memory_edge_loop #(parameter integer W = 8, N = 4) (
    input wire clk,
    input wire rstn,
    input wire [W-1:0] d,
    output wire [W-1:0] q
);
    logic [W-1:0] mem [N];
    integer i;
    always_ff @(posedge clk or negedge rstn) begin
        if (!rstn)
            for (i = 0; i < N; i = i + 1) mem[i] <= '0;
        else
            for (i = 0; i < N; i = i + 1) mem[i] <= d;
    end
    assign q = mem[0];
endmodule
