module default_point_array_e(input logic clk, input logic [7:0] d, output logic [7:0] q);
  logic [7:0] pipe [0:3];
  integer i;
  always_ff @(posedge clk) begin
    pipe[0] <= d;
    for (i = 1; i < 4; i = i + 1) pipe[i] <= pipe[i-1];
  end
  assign q = pipe[3];
endmodule
