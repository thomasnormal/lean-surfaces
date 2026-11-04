// A FLAT netlist: a 4-bit ripple-carry adder written out gate by gate. No parameter, no generate loop:
// every site is plain (`plain#0` ... `plain#9`, in source order). `sv_structure` closes the structural
// obligations of such a design by deciding closed statements about the site list instead of normalizing
// them (WP-P3b); see `comb_view.lean`. The LAST assign drives a bit of a vector output, the shape that
// used to make `sv_equations` give up naming its equations (`comb_hint.lean`).
module flat_net (
  input  logic [3:0] a, b,
  input  logic       cin,
  output logic [3:0] s,
  output logic       cout
);
  logic [4:0] c;
  assign c[0]  = cin;
  assign s[0]  = a[0] ^ b[0] ^ c[0];
  assign c[1]  = (a[0] & b[0]) | (c[0] & (a[0] ^ b[0]));
  assign s[1]  = a[1] ^ b[1] ^ c[1];
  assign c[2]  = (a[1] & b[1]) | (c[1] & (a[1] ^ b[1]));
  assign s[2]  = a[2] ^ b[2] ^ c[2];
  assign c[3]  = (a[2] & b[2]) | (c[2] & (a[2] ^ b[2]));
  assign c[4]  = (a[3] & b[3]) | (c[3] & (a[3] ^ b[3]));
  assign cout  = c[4];
  assign s[3]  = a[3] ^ b[3] ^ c[3];   // LAST in source order, and a bit of a vector output
endmodule
