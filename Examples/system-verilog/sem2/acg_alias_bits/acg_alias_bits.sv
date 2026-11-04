// REFUSED by the always_comb alias guard (`AlwaysComb:alias-read`,
// LeanModels/Sv/CombAlias2.lean), at BIT granularity: `w` copies all of `t`;
// the block reads `w` and then writes t[1], while t[0] has its own
// continuous driver (legal: each bit of a packed type is an independent
// element, IEEE 1800-2023 §6.5/§9.2.2.2). The bit the block writes (t[1]) is
// one of the bits `w` copies, so the read of `w` precedes a write of its
// source. Icarus 12.0 shows y one change behind; the model gives the settled
// value. Compare `acg_alias_bits_ok`, where `w` copies only t[0], which the
// block does not write (admitted).
module acg_alias_bits (
  input  logic a, b,
  output logic [1:0] y
);
  logic [1:0] t;
  logic [1:0] w;
  assign t[0] = b;
  assign w = t;
  always_comb begin
    y = w;
    t[1] = a;
  end
endmodule
