// A FLAT netlist that has a PARAMETER: a 12-bit ripple-carry adder written out gate by gate (26 plain sites, no
// generate loop) inside a module with a configuration parameter `K` that the body does not use. Every site is
// plain, but the instantiated design mentions the free variable `K`, so `sv_structure` and `sv_equations` cannot
// DECIDE its obligations as closed statements (the flat-netlist fast path needs a parameter-free design) and take
// the normalization route. Its coverage obligations then carry one `∃ b, (b = site₀ ∨ … ∨ b = site₂₅) ∧ …`
// goal per read, which `sv_cover` closes by picking the writer's site by name (see `sv_cover_site.lean`).
module flat_net_p #(parameter int K = 0) (
  input  logic [11:0] a, b,
  input  logic        cin,
  output logic [11:0] s,
  output logic        cout
);
  logic [12:0] c;
  assign c[0] = cin;
  assign s[0] = a[0] ^ b[0] ^ c[0];
  assign c[1] = (a[0] & b[0]) | (c[0] & (a[0] ^ b[0]));
  assign s[1] = a[1] ^ b[1] ^ c[1];
  assign c[2] = (a[1] & b[1]) | (c[1] & (a[1] ^ b[1]));
  assign s[2] = a[2] ^ b[2] ^ c[2];
  assign c[3] = (a[2] & b[2]) | (c[2] & (a[2] ^ b[2]));
  assign s[3] = a[3] ^ b[3] ^ c[3];
  assign c[4] = (a[3] & b[3]) | (c[3] & (a[3] ^ b[3]));
  assign s[4] = a[4] ^ b[4] ^ c[4];
  assign c[5] = (a[4] & b[4]) | (c[4] & (a[4] ^ b[4]));
  assign s[5] = a[5] ^ b[5] ^ c[5];
  assign c[6] = (a[5] & b[5]) | (c[5] & (a[5] ^ b[5]));
  assign s[6] = a[6] ^ b[6] ^ c[6];
  assign c[7] = (a[6] & b[6]) | (c[6] & (a[6] ^ b[6]));
  assign s[7] = a[7] ^ b[7] ^ c[7];
  assign c[8] = (a[7] & b[7]) | (c[7] & (a[7] ^ b[7]));
  assign s[8] = a[8] ^ b[8] ^ c[8];
  assign c[9] = (a[8] & b[8]) | (c[8] & (a[8] ^ b[8]));
  assign s[9] = a[9] ^ b[9] ^ c[9];
  assign c[10] = (a[9] & b[9]) | (c[9] & (a[9] ^ b[9]));
  assign s[10] = a[10] ^ b[10] ^ c[10];
  assign c[11] = (a[10] & b[10]) | (c[10] & (a[10] ^ b[10]));
  assign s[11] = a[11] ^ b[11] ^ c[11];
  assign c[12] = (a[11] & b[11]) | (c[11] & (a[11] ^ b[11]));
  assign cout = c[12];
endmodule
