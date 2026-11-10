// Clean-room IEEE 1800-2023 §§9.4.2.2 and 27: the implicit event stays
// inside its generate branch/template. No process is rewritten to comb.
module always_star_generate_step11 #(
    parameter integer W = 4,
    parameter integer USE_A = 1,
    parameter integer LANES = 2
) (
    input logic [W-1:0] a, b,
    input logic [LANES-1:0] lane_a,
    output logic [W-1:0] y,
    output logic [LANES-1:0] lane_y
);
    generate
        if (USE_A) begin : use_a
            always @* y = a;
        end else begin : use_b
            always @* y = b;
        end
        for (genvar i = 0; i < LANES; i = i + 1) begin : lanes
            always @* lane_y[i] = lane_a[i] ^ a[0];
        end
    endgenerate
endmodule
