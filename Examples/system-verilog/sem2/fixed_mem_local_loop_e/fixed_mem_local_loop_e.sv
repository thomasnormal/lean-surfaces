module fixed_mem_local_loop_e #(parameter int W = 8) (input logic clk, input logic [W-1:0] d, input logic [1:0] idx, output logic [W-1:0] q);
  logic [W-1:0] s [0:3];
  always_ff @(posedge clk) begin
    for (int i = 1; i < 4; i++) s[i] <= s[i-1];
    s[0] <= d;
    s[idx] <= d;
  end
  assign q = s[1];
endmodule
