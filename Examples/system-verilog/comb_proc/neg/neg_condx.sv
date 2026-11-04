// WP-G negative fixture neg_condx: the condition reads u[i], which nothing drives: the read has no source, so the Boolean equation cannot be justified (cover obligation)
module neg_condx #(parameter int N = 4) (
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
        if (u[i]) c[i+1] = c[i];
        else      c[i+1] = a[i];
      end
      assign s[i] = p[i] ^ c[i];
    end
  endgenerate
  assign cout = c[N];
endmodule
