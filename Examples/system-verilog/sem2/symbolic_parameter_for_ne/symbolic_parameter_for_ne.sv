// A reaching != bound is exact after parameter binding.
module symbolic_parameter_for_ne #(
  parameter int N = 4
) (
  input logic [7:0] a,
  output logic [7:0] y
);
  always_comb begin
    y = 8'b0;
    for (int i = 0; i != N; i++)
      y[i] = a[i];
  end
endmodule
