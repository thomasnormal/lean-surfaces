// WP-G S2: `always_comb` bodies whose conditions and right-hand sides use the new operators. `!p` as a
// condition (the swapped twin of `if (p)` in the known regime), `&&`/`||`/`==`, a reduction, `~` and `?:` in a leaf.
module ops_proc #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic [N-1:0] v,
  output logic [N-1:0] y, z,
  output logic         w
);
  logic [N-1:0] p;
  assign p = a ^ b;
  assign z = ~p;
  always_comb begin
    if (!p[0] && (a[0] || b[0])) y = ~a;
    else if (|v) y = b;
    else y = (a == b) ? a : v;
  end
  always_comb begin
    if (a[0] == b[0]) w = &v;
    else w = !a[0] ? ~b[0] : v[0];
  end
endmodule
