// Clean-room Step 11 fixture: a runtime bit-select is the target of an NBA
// inside always_ff.  The index is deliberately wider than the vector so the
// x/z and out-of-range target rules remain observable.
module dynamic_nba_target_step11 (
    input  logic       clk,
    input  logic [2:0] idx,
    input  logic       d,
    input  logic       en,
    output logic [3:0] q
);
    always_ff @(posedge clk) begin
        if (en)
            q[idx] <= d;
    end
endmodule
