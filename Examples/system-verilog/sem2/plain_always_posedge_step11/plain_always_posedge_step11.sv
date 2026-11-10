// Clean-room Step 11 fixture: a plain always @(posedge) with NBA-only body.
// It is intentionally source-shaped, rather than rewritten to always_ff.
module plain_always_posedge_step11 (
    input  logic       clk,
    input  logic       en,
    input  logic [3:0] d,
    output logic [3:0] q,
    output logic [3:0] q_copy
);
    always @(posedge clk) begin
        if (en)
            q <= d;
        else
            q <= 4'hA;
        q_copy <= d;
    end
endmodule
