// ADMITTED by the always_comb alias guard (LeanModels/Sv/CombAlias2.lean):
// a continuous copy `w` of an INPUT, read by a block that writes other
// variables. No path from a write of the block to `w` exists, so nothing is
// refused: the guard changes nothing on the common pattern.
module acg_alias_far (
  input  logic [1:0] a, b,
  output logic [1:0] y, z
);
  logic [1:0] w;
  assign w = a;
  always_comb begin
    y = w;
    z = b;
  end
endmodule
