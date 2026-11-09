// One parameterized leaf, instantiated twice: each copy computes the XOR of one half of the word.
module halves_leaf #(parameter integer W = 4) (input logic [W-1:0] a, input logic [W-1:0] b,
                                              output logic [W-1:0] y);
  assign y = a ^ b;
endmodule

module halves #(parameter integer W = 8) (input logic [W-1:0] a, input logic [W-1:0] b,
                                          output logic [W-1:0] y);
  localparam integer H = W / 2;
  halves_leaf #(.W(W / 2)) lo (.a(a[H-1:0]), .b(b[H-1:0]), .y(y[H-1:0]));
  halves_leaf #(.W(W / 2)) hi (.a(a[W-1:H]), .b(b[W-1:H]), .y(y[W-1:H]));
endmodule
