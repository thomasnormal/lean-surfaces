// ADMITTED by the always_comb alias guard (LeanModels/Sv/CombAlias2.lean):
// WRITE THEN READ through a continuous copy. The block writes `t` and only
// then reads `w = t`, so on every path the read comes after the last write of
// its source; every tool agrees (y = a): Xcelium 24.03 and Verilator 5.042
// read the old `w`, then re-run the block; Icarus 12.0 updates `w` inside the
// block's run and reads the new one. Compare `acg_alias_assign`, the same
// block with the two statements swapped (refused).
module acg_alias_wr (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] t, w;
  assign w = t;
  always_comb begin
    t = a;
    y = w;
  end
endmodule
