// A non-ANSI child with an initialized output variable under an ANSI parent.
// Since round 4 (Lane A) the child's always_ff block is REFUSED
// (`ProceduralBlockSymbol:initialized-variable`: Xcelium 24.03
// `*E,MULAXX`); `pi_hier_plain` pins the form with a plain `always`.
module pi_nonansi_hier_c(clk, a, o);
  input clk;
  input a;
  output [1:0] o;
  logic [1:0] o = 2'b10;
  always_ff @(posedge clk) o[0] <= a;
endmodule
module pi_nonansi_hier(input logic clk, input logic a, output logic [1:0] y);
  pi_nonansi_hier_c u(.clk(clk), .a(a), .o(y));
endmodule
