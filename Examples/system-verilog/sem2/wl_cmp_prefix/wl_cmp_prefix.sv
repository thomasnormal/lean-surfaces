// WP-B2 pin P6: comparisons whose operands have a per-instance width (the prefixes a[i-1:0], b[i-1:0] of a generate loop) and a `~` inside an operand; the carry of a prefix as `a_i > ~b_i | (a_i == ~b_i) & cin`.
module wl_cmp_prefix #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic cin,
  output logic [N:0] c
);
  assign c[0] = cin;
  for (genvar i = 1; i < N + 1; i++) begin : g
    assign c[i] = (a[i-1:0] > ~b[i-1:0]) | ((a[i-1:0] == ~b[i-1:0]) & cin);
  end
endmodule
