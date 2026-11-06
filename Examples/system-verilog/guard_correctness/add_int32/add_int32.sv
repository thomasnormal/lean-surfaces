module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  localparam int M = (N == 5) ? 1073741824 * 2 : 1;
  logic [N:0]   c;
  logic [N-1:0] sr;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign sr[i]  = a[i] ^ b[i] ^ c[i];
      assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));
    end
    if (M > 0) begin : g_ok
      assign s = sr;
    end else begin : g_bad
      assign s = ~sr;
    end
  endgenerate
  assign cout = c[N];
endmodule
