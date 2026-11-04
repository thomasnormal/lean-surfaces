// ADMITTED by the always_comb alias guard (LeanModels/Sv/CombAlias2.lean), at
// BIT granularity: `w` copies t[0], which has its own continuous driver, and
// the block writes t[1] after reading `w`. The block reads no bit downstream
// of a bit it writes, so a signal-level check (t is written later) would
// refuse this and the bit-level one does not. Compare `acg_alias_bits`, where
// `w` copies all of `t` (refused).
module acg_alias_bits_ok (
  input  logic a, b,
  output logic y
);
  logic [1:0] t;
  logic w;
  assign t[0] = b;
  assign w = t[0];
  always_comb begin
    y = w;
    t[1] = a;
  end
endmodule
