// Parameter-sized unpacked storage retained as one source-shaped MemE memory.
module memory_shape_a_e #(parameter integer W = 4, parameter integer P = 3) (
    input logic clk,
    input logic [W-1:0] d,
    input logic [2:0] idx,
    output logic [W-1:0] q,
    output logic [W-1:0] selected
);
    logic [W-1:0] s [P];
    always_ff @(posedge clk) begin
      for (int i = 1; i < P; i++) s[i] <= s[i-1];
      s[0] <= d;
    end
    assign q = s[P-1];
    assign selected = s[idx];
endmodule
