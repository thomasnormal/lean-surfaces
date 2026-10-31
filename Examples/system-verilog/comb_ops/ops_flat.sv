// WP-G S2: a FLAT netlist (no parameter, no loop) with all the new operators: the obligations are decided
// by the tactics (`decided (flat netlist ...)`), and the hit of `!`, `&&`, `||`, `?:`, `==`, reductions.
module ops_flat (
  input  logic [3:0] a, b,
  input  logic       s, t,
  output logic [3:0] y, z,
  output logic       p, q, r, u
);
  logic [3:0] n;
  logic       w;
  assign n = ~(a ^ b);
  assign w = !(s && t);
  assign y = w ? n : (a & b);
  assign z = s ? ~a : b;
  assign p = |y;
  assign q = (a == b) || (s != t);
  assign r = &n;
  assign u = ~^z;
endmodule
