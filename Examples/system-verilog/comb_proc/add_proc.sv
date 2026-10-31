// svGolf task `add`, reference solution (WP-G): a ripple-carry adder whose CARRY CELL is an
// `always_comb` body inside the generate loop. p[i] is the propagate bit; when p[i] the carry
// out is the carry in, otherwise the operands agree and carry their common value a[i].
// c[0] = cin, cout = c[N].
module add_proc #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0]   c;
  logic [N-1:0] p;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign p[i] = a[i] ^ b[i];
      always_comb begin
        if (p[i]) c[i+1] = c[i];
        else      c[i+1] = a[i];
      end
      assign s[i] = p[i] ^ c[i];
    end
  endgenerate
  assign cout = c[N];
endmodule
