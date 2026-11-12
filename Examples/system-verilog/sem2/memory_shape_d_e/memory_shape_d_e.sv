// Source-shaped fixed unpacked storage with a loop-local index.
module memory_shape_d_e #(parameter integer W = 4) (
    input logic clk,
    input logic [W-1:0] d,
    input logic [1:0] idx,
    output logic [W-1:0] q,
    output logic [W-1:0] selected
);
    logic [W-1:0] s [0:3];
    always_ff @(posedge clk) begin
      for (int i = 1; i < 4; i++) s[i] <= s[i-1];
      s[0] <= d;
    end
    assign q = s[3];
    assign selected = s[idx];
endmodule
