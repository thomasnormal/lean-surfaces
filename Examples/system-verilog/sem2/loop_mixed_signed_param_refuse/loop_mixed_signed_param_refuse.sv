// A parameter expression with an unsigned operand keeps the comparison unsigned.
module loop_mixed_signed_param_refuse #(
  parameter int N = 4
) (
  input  logic [7:0] d,
  output logic [7:0] q
);
  localparam logic [1:0] P = 2;
  always_comb begin
    q = 8'h00;
    for (int i = -1; i < P + N - N; i++)
      q[i + 1] = d[i + 1];
  end
endmodule
