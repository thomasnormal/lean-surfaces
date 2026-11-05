module nonaffine #(parameter int N = 4) (
  input logic [N-1:0] a,
  output logic [N-1:0] s
);
  genvar i;
  for (i = 0; i < N; i++) begin : g_bit
    assign s[i] = a[(i >> 1) << 1];
  end
endmodule
