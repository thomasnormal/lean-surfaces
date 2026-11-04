// The ripple-carry adder of `ripple_add`, written structurally: one
// `full_adder` instance per bit, instantiated by a generate loop.
module full_adder (
  input  logic a, b, cin,
  output logic s, cout
);
  assign s    = a ^ b ^ cin;
  assign cout = (a & b) | (cin & (a ^ b));
endmodule

module ripple_fa #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0] c;
  assign c[0] = cin;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_bit
      full_adder fa (.a(a[i]), .b(b[i]), .cin(c[i]), .s(s[i]), .cout(c[i+1]));
    end
  endgenerate
  assign cout = c[N];
endmodule
