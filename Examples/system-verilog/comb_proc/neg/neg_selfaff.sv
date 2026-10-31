// WP-G negative fixture neg_selfaff: the body reads the window it writes (c[i+1] ^ a[i]): the self-read the CombGuard2 rule and selfReadFree refuse
module neg_selfaff #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0]   c;
  logic [N-1:0] p, u;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign p[i] = a[i] ^ b[i];
      always_comb begin
        if (p[i]) c[i+1] = c[N-i] ^ a[i];
        else      c[i+1] = a[i];
      end
      assign s[i] = p[i] ^ c[i];
    end
  endgenerate
  assign cout = c[N];
endmodule
