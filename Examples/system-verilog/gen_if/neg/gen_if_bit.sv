// A generate condition that tests a bit of a genvar (`(i & 1) == 0`): `&` is outside the guard fragment.
module gen_if_bit #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      if ((i & 1) == 0) begin : g_even
        assign y[i] = a[i];
      end else begin : g_odd
        assign y[i] = 1'b0;
      end
    end
  endgenerate
endmodule
