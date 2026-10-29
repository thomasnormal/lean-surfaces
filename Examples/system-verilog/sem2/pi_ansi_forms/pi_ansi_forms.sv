// Output-port declaration initializers, ANSI forms (2026-10-28, round 4
// Lane A): `output logic`, `output reg` and `output var logic` with an
// initializer, a few bits rewritten by a PLAIN `always` (an
// `always_ff` / `always_comb` writer of an initialized variable is refused,
// `ProceduralBlockSymbol:initialized-variable`). slang keeps an ANSI port's
// initializer on the port symbol; the Port carries it as `init`. Measured
// on one batched testbench of the `pi_*` fixtures: Icarus 12.0, Xcelium
// 24.03 (refsim on vip-ng), Verilator 5.042 (x read as 0) and the Yosys
// 0.53 `synth -flatten; abc -g gates` netlist give the same initial values.
// (`output var [1:0] y4 = 2'b10`, an implicit data type, emits its
// initializer too, but the symbolic tier does not recover an implicit
// type's packed dimensions, so that port is loud for an unrelated reason:
// crossCheck "unrecoverable packed dimensions".)
module pi_ansi_forms (
  input  logic           clk,
  input  logic           a,
  output logic     [1:0] y1 = 2'b10,
  output reg       [1:0] y2 = 2'b01,
  output var logic [1:0] y3 = 2'b11
);
  always @(posedge clk) begin
    y1[0] <= a;
    y3[1] <= a;
  end
endmodule
