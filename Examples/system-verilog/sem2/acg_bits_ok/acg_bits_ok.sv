// Bits, not whole variables (ADMITTED): bit 0 of `t` is written before it is
// read; bit 1 is written after the read of bit 0 but is not read before.
// Admitted by the always_comb self-read guard (LeanModels/Sv/CombGuard2.lean).
module acg_bits_ok (
  input  logic a, b,
  output logic y, z
);
  logic [1:0] t;
  always_comb begin
    t[0] = a;
    y = t[0];
    t[1] = b;
    z = t[1];
  end
endmodule
