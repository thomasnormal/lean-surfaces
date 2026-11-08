// Clean-room wall: a variable initializer reads a signal at time zero.
module nonliteral_initializer(input logic a, output logic [1:0] q);
  logic [1:0] t = a;
  assign q = t;
endmodule
