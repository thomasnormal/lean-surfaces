// IEEE 1800-2023 §§10.4.2, 11.5.1: selects and values are sampled at issue.
module dynamic_nba_issue_step11 (
    input logic clk,
    input logic reset,
    input logic [2:0] idx, idx2,
    input logic signed [2:0] sidx,
    input logic [1:0] d,
    output logic [1:0] cursor,
    output logic [3:0] q, signed_q, old_q,
    output logic [3:0][1:0] words,
    output logic [7:0] old_words
);
    always_ff @(posedge clk) begin
        if (reset) begin
            cursor <= 2'b00;
            q <= 4'b1010;
            signed_q <= 4'b0101;
            words <= 8'h96;
            old_q <= 4'b0000;
        end else begin
            cursor <= idx[1:0];
            q[cursor] <= d[0];
            q[idx] <= d[1];
            q[idx2] <= d[0];
            signed_q[sidx] <= d[0];
            words[idx] <= d;
            old_q <= q;
        end
    end
    always_ff @(posedge clk) old_words <= words;
endmodule
