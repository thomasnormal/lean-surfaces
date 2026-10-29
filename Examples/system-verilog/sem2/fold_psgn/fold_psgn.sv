// Round 5 folds (verifier repros vq_sgn2, vq_sgn3): the declared signedness
// of a parameter whose width depends on another parameter. The envelope
// omitted `signed` wherever it matched "signed exactly when 32 bits wide" at
// the DEFAULT point, and the constant tier applied that rule at each point's
// width: S (signed, 32 bits by default) was read unsigned at M = 8, and U
// (unsigned, 8 bits by default) signed at N = 32.
module fold_psgn #(parameter int M = 32, parameter logic signed [M-1:0] S = -1,
                   parameter int N = 8, parameter logic [N-1:0] U = -1) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o5, o6,
  output logic [31:0] o3,
  output logic o4);
  localparam integer I = S >>> 1;
  localparam logic [N-1:0] L = U >>> 1;
  assign o1 = S;
  assign o2 = S + a;
  assign o3 = I;
  assign o4 = S < 0;
  assign o5 = L;
  assign o6 = U >>> 1;
endmodule
