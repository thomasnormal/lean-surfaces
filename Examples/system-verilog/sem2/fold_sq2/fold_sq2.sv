// Round 5 folds (verifier repro vq_sq2): 2-state typed constants whose width
// depends on a parameter. slang wraps each initializer in a same-width
// 4-state -> 2-state conversion sized at the DEFAULT point (`Squash2`, 32 bits
// at N = 32); the constant tier read that width as a floor, so at N = 4 the
// localparams were evaluated at 32 bits (8, 1, 4) where every tool gives 0.
module fold_sq2 #(parameter int N = 32, parameter logic [N-1:0] U = -1,
                  parameter bit [N-1:0] PB = (U + 1'b1) >> 1) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o3, o4, o5);
  localparam bit [N-1:0] B1 = (U + 1'b1) >> 1;
  localparam bit [N-1:0] B2 = (U + 1'b1) % 3'd5;
  localparam bit [N-1:0] B3 = (U + 1'b1) >>> 2;
  localparam int K = (U + 1'b1) >> 1;
  assign o1 = B1;
  assign o2 = B2;
  assign o3 = B3;
  assign o4 = PB;
  assign o5 = K;
endmodule
