// WP-G S3b: the carry cell of `comb_proc/add_proc.sv` written as DEFAULT-THEN-OVERRIDE, the way a player
// often writes it: the carry out defaults to the generate bit a[i], and when p[i] (the operands differ)
// the carry in overrides it. The last write wins; the lowered equation is the same `p[i] ? c[i] : a[i]`.
module add_ovr #(parameter int N = 16) (
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
        c[i+1] = a[i];
        if (p[i]) c[i+1] = c[i];
      end
      assign s[i] = p[i] ^ c[i];
    end
  endgenerate
  assign cout = c[N];
endmodule
