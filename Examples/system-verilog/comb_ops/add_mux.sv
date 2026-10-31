// WP-G S2: a ripple-carry adder written with `~` and `?:`. e[i] = (a[i] == b[i]) is the XNOR of the operand
// bits; when they agree the carry out is their common value a[i], otherwise it is the carry in c[i]; the sum
// bit is the XNOR of e[i] and c[i] (= a[i] ^ b[i] ^ c[i]). c[0] = cin, cout = c[N].
module add_mux #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0]   c;
  logic [N-1:0] e;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      assign e[i] = ~(a[i] ^ b[i]);
      assign c[i+1] = e[i] ? a[i] : c[i];
      assign s[i] = ~(e[i] ^ c[i]);
    end
  endgenerate
  assign cout = c[N];
endmodule
