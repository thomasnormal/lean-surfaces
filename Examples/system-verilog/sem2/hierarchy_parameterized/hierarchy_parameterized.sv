// Refused construct: a parameterized module instance in a generated arithmetic wrapper.
// Refused by: sv_structure.
// Exact message: this design instantiates modules, and the hierarchy summary (`CombHier.lean`) does not read it: the module has a member outside the semantic tier (`PortSymbol:net-z`: y), which the instantiation keeps as a loud process.
module leaf #(parameter integer W = 4) (input wire [W-1:0] a, output wire [W-1:0] y);
  assign y = a;
endmodule
module hierarchy_parameterized #(parameter integer W = 8) (input wire [W-1:0] a, output wire [W-1:0] y);
  leaf #(.W(W/2)) lo(.a(a[W/2-1:0]), .y(y[W/2-1:0]));
  leaf #(.W(W/2)) hi(.a(a[W-1:W/2]), .y(y[W-1:W/2]));
endmodule
