// Clean-room canonical-E row: always_comb beside source-shaped memory.
module always_comb_memory_canonical_e #(parameter integer W = 4) (
    input logic clk,
    input logic en,
    input logic [W-1:0] d,
    output logic [W-1:0] q
);
    logic [W-1:0] mem [0:1];

    always_comb begin
      q = mem[0];
      if (en)
        q = d;
    end

    always_ff @(posedge clk)
      mem[0] <= d;
endmodule
