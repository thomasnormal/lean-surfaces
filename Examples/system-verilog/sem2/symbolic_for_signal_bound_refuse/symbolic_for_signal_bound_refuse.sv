// A runtime signal bound needs scoped loop state and remains loud.
module symbolic_for_signal_bound_refuse (
  input logic [2:0] limit,
  input logic [7:0] a,
  output logic [7:0] y
);
  always_comb begin
    y = 8'b0;
    for (int i = 0; i < limit; i++)
      y[i] = a[i];
  end
endmodule
