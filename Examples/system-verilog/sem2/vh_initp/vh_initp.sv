// A child's initialized output port partly driven by `assign` (2026-10-28,
// round 4 Lane A): the §6.5 continuous/procedural mixture (`vg_initp`)
// inside a hierarchy. Icarus 12.0 "Unable to assign to unresolved wires",
// Xcelium 24.03 `*E,ICDDIV` (illegal combination of driver and declaration
// initializer), Yosys 0.53 a conflicting constant driver; loud
// (`ContinuousAssignSymbol:initialized-variable`, in the child).
module vh_initp_c (
  input  logic       a,
  output logic [1:0] o = 2'b10
);
  assign o[0] = a;
endmodule

module vh_initp (
  input  logic       a,
  output logic [1:0] y
);
  vh_initp_c u (.a(a), .o(y));
endmodule
