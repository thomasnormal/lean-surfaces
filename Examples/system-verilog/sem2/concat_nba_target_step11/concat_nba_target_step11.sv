// Clean-room Step 11 fixture: one packed vector is written through two
// disjoint windows of the same signal in one nonblocking concatenation.
// IEEE 1800-2023 §10.6 preserves the source-shaped concatenation target.
module concat_nba_target_step11 (
    input  logic       clk,
    input  logic [7:0] d,
    output logic [7:0] q
);
    always_ff @(posedge clk) begin
        {q[7:4], q[3:0]} <= d;
    end
endmodule
