module guarded #(parameter int N = 4) (
  input logic [N-1:0] a,
  input logic [N-1:0] b,
  output logic [N-1:0] s
);
  genvar i;
  for (i = 0; i < N; i++) begin : g_bit
    if (i == 0) begin : g_lo
      assign s[i] = a[i];
    end else begin : g_hi
      assign s[i] = b[i];
    end
  end
endmodule
