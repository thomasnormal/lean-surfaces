module param_mem_shift_e #(parameter int W = 8, parameter int P = 4) (
  input logic clk, input logic [W-1:0] d, output logic [W-1:0] q);
  logic [W-1:0] s [P];
  always_ff @(posedge clk) begin
    for (int i = 1; i < P; i++) s[i] <= s[i-1];
    s[0] <= d;
  end
  assign q = s[0];
endmodule
