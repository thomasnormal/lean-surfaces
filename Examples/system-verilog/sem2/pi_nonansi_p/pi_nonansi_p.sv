// A parametric non-ANSI output variable with an initializer.
// Since round 4 (Lane A) the always_ff block is REFUSED at every N
// (`ProceduralBlockSymbol:initialized-variable`: Xcelium 24.03
// `*E,MULAXX`); `pi_width_p` pins a parametric initializer with a plain
// `always`.
module pi_nonansi_p(clk, a, y);
  parameter int N = 3;
  input clk;
  input a;
  output [N-1:0] y;
  logic [N-1:0] y = '1;
  always_ff @(posedge clk) y[0] <= a;
endmodule
