// An int iterator compared with an unsigned bound is an unsigned SV compare.
module loop_mixed_signed_refuse (
  input  logic [7:0] d,
  output logic [7:0] q
);
  always_comb begin
    q = 8'h00;
    for (int i = -1; i < 2'd2; i++)
      q[i + 1] = d[i + 1];
  end
endmodule
