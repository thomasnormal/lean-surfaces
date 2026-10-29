// Output-port declaration initializers, NON-ANSI forms (2026-10-28, round 4
// Lane A): the variable declared separately as `logic`, `reg` or
// `var logic` with the initializer (slang keeps it on the internal
// variable), a single `output reg` / `output logic` declaration with one
// (slang keeps it on the port symbol), two identifiers sharing one
// declaration, and a scalar; a few bits rewritten by a PLAIN `always`.
// Icarus 12.0, Xcelium 24.03 (refsim on vip-ng), Verilator 5.042 and the
// Yosys 0.53 netlist give the same initial values. (The non-ANSI
// `output var logic [1:0] y = ...;` single declaration is legal and admitted
// too, but Icarus 12.0 does not parse it, so it is pinned by the extractor
// tests only.)
module pi_nonansi_forms (clk, a, z1, z2, z3, z4, z5, z6, z7, z8);
  input clk;
  input a;
  output [1:0] z1;
  logic [1:0] z1 = 2'b10;
  output [1:0] z2;
  reg [1:0] z2 = 2'b01;
  output [1:0] z3;
  var logic [1:0] z3 = 2'b11;
  output reg [1:0] z4 = 2'b10;
  output logic [1:0] z5 = 2'b01;
  output reg [1:0] z6 = 2'b10, z7 = 2'b01;
  output z8;
  reg z8 = 1'b1;
  always @(posedge clk) begin
    z1[0] <= a;
    z2[1] <= a;
    z4[0] <= a;
    z6[1] <= a;
  end
endmodule
