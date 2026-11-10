// IEEE 1800-2023 §§9.2.2.1, 9.2.2.4, 9.4.2.3: event guards belong to the source.
module plain_always_reset_metadata_step11 (
    input logic clk, rn, gate, d,
    output logic q, r
);
    always @(posedge clk or negedge rn)
        if (!rn) q <= 1'b0;
        else q <= d;
    always_ff @(posedge clk or negedge rn iff gate)
        if (!rn) r <= 1'b0;
        else r <= d;
endmodule
