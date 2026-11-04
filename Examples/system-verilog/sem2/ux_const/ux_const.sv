// An unsized x/z literal widened in a CONSTANT position (round 5 Lane A,
// 2026-10-29). The `case` item is the shape this newly refuses: `'hx0`
// against a 40-bit `b` is x-padded by Icarus 12.0 and by Yosys 0.53's
// `prep`, but the synthesized netlist reads the x as a don't-care (at b =
// 00000000 then 28 x then 0000: Icarus y3 = 2, netlist 1); 2e8c8b28
// zero-padded the item (at b = 36 x then 0000: model 2, both tools 1) and
// round 4 followed Icarus. The localparam `LP = 'hx0` and the override
// `.P('hz1)` split too (Icarus pads with the x/z bit, Yosys and slang's
// constant with zeros), but the Lean constant tier refuses every x/z
// constant, so they were loud before and stay loud. Now every such
// widening in a constant position is `ConversionExpression:unsized-xz-
// constant` in the extractor.
module ux_const_c #(
  parameter logic [39:0] P = 40'd0
) (
  output logic [39:0] o
);
  assign o = P;
endmodule

module ux_const (
  input  logic        clk,
  input  logic [39:0] b,
  output logic [39:0] y1,
  output logic [39:0] y2,
  output logic [7:0]  y3
);
  localparam logic [39:0] LP = 'hx0;
  assign y1 = LP;
  ux_const_c #(.P('hz1)) u (.o(y2));
  always_comb begin
    case (b)
      'hx0:    y3 = 8'd1;
      default: y3 = 8'd2;
    endcase
  end
endmodule
