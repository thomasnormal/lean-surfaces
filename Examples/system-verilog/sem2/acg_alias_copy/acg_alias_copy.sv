// ADMITTED by the always_comb alias guard (LeanModels/Sv/CombAlias2.lean):
// the copy `w` is made by a SEPARATE always_comb block, not an `assign`. A
// process is woken by an update of its inputs like any other, in every tool
// (y = a, Icarus 12.0 included), so the read-before-write order inside the
// second block is harmless. Compare `acg_alias_assign`, where the copy is an
// `assign` (refused).
module acg_alias_copy (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] t, w;
  always_comb w = t;
  always_comb begin
    y = w;
    t = a;
  end
endmodule
