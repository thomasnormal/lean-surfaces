// The halves at an odd width: the low half takes `(W+1)/2` bits. A quotient of a sum is not one of the affine forms the
// summary reads (`n / d` of one named constant is).
module odd_leaf #(parameter integer W = 4) (input wire [W-1:0] a, output wire [W-1:0] y);
  assign y = a;
endmodule
module odd_split #(parameter integer W = 7) (input wire [W-1:0] a, output wire [W-1:0] y);
  odd_leaf #(.W((W+1)/2)) lo(.a(a[(W+1)/2-1:0]), .y(y[(W+1)/2-1:0]));
  odd_leaf #(.W(W/2)) hi(.a(a[W-1:(W+1)/2]), .y(y[W-1:(W+1)/2]));
endmodule
