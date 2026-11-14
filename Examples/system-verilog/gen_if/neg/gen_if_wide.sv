// A generate condition whose operand leaves the 32-bit range for large `N` (`i + N * 1024 > 0`): read, but its
// 32-bit obligation fails without a bound on `N` that keeps `N * 1024` an `int`.
module gen_if_wide #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      if (i + N * 1024 > 0) begin : g_on
        assign y[i] = a[i];
      end else begin : g_off
        assign y[i] = 1'b0;
      end
    end
  endgenerate
endmodule
