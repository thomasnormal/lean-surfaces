// A self-reading always_comb inside a CHILD instance: `t[1]` is read before
// it is written on the only path and written later (`t[0] = a; y = t[1];
// t[1] = b;`). The always_comb self-read guard refuses the child's block
// (`AlwaysComb:self-read`, LeanModels/Sv/CombGuard2.lean) and the refusal
// names the instance and the child module (`instBodyProc`,
// LeanModels/Sv/Hier2.lean); load_design_sv2 refuses this envelope.
// The settle semantics would give y = b; Icarus 12 shows the PREVIOUS b
// (IEEE 1800-2023 9.2.2.2.1).
module rbw_child_leaf (
  input  logic a, b,
  output logic y
);
  logic [1:0] t;
  always_comb begin
    t[0] = a;
    y = t[1];
    t[1] = b;
  end
endmodule

module rbw_child (
  input  logic a, b,
  output logic y
);
  rbw_child_leaf u (.a(a), .b(b), .y(y));
endmodule
