// Refused construct: a wire driven by assignments inside a generate loop.
// Tool: sv_structure (gates ~27 blocks).
// Exact message: out-of-tier module members are present
module wire_generate #(parameter integer W = 8) (
    input logic [W-1:0] x,
    output wire [W-1:0] y
);
    genvar i;
    generate
        for (i = 0; i < W; i = i + 1)
            assign y[i] = x[i];
    endgenerate
endmodule
