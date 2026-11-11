// Clean-room Step 10 fixture: two comb stages beside one NBA edge process.
// The second comb stage must settle again after the edge commits q.
module mixed_core_step10 (
    input  logic       clk,
    input  logic       en,
    input  logic [3:0] d,
    output logic [3:0] q,
    output logic [3:0] n,
    output logic [3:0] post
);
    always_comb n = q ^ d;
    always_comb post = n + 4'h1;

    always_ff @(posedge clk) begin
        if (en)
            q <= d;
        else
            q <= ~d;
    end
endmodule
