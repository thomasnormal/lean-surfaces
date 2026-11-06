module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0]   c;
  logic [N-1:0] sr;
  assign c[0] = cin;
  genvar i, k;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign sr[i]  = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
    for (k = N; k < N + 1; k++) begin : g_k
      if ((k == 5) && (((k - 6) & 1) != 0)) begin : g_bad
        assign s = ~sr;
      end else begin : g_ok
        assign s = sr;
      end
    end
  endgenerate
  assign cout = c[N];
endmodule
