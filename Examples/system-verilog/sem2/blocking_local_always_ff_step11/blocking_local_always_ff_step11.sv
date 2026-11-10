// Clean-room Step 11 fixture: a block-local temporary is written with
// blocking assignments, then sampled by nonblocking architectural updates.
// IEEE 1800-2023 §9.2.2.4 permits the always_ff process to update its local
// variable; the E edge profile must preserve the local's sequential scope.
module blocking_local_always_ff_step11 (
    input  logic       clk,
    input  logic [3:0] d,
    output logic [3:0] q,
    output logic [3:0] q_not
);
    always_ff @(posedge clk) begin : capture
        logic [3:0] t;
        t = d;
        q <= t;
        t = ~t;
        q_not <= t;
    end
endmodule
