// Round 3 folds, CX verifier major: a NON-ANSI output port whose variable is
// declared separately WITH an initializer (`output [1:0] y; logic [1:0] y =
// 2'b10;`). slang keeps that initializer on the internal variable, not on
// the port symbol, and the Port used to drop it (`y` read x1 for 11).
// Since round 4 (Lane A) the always_ff block is REFUSED
// (`ProceduralBlockSymbol:initialized-variable`: Xcelium 24.03
// `*E,MULAXX`); `pi_nonansi_forms` pins the form with a plain `always`.
module pi_nonansi(clk, a, y);
  input clk;
  input a;
  output [1:0] y;
  logic [1:0] y = 2'b10;
  always_ff @(posedge clk) y[0] <= a;
endmodule
