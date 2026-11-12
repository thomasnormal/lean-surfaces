module for_loop_e(input logic clk, input logic [7:0] d, output logic [7:0] q);
  logic [7:0] values [0:3];
  integer i;
  always_ff @(posedge clk) begin
    for (i = 1; i < 4; i = i + 1) values[i] <= values[i-1];
    values[0] <= d;
  end
  assign q = values[3];
endmodule
