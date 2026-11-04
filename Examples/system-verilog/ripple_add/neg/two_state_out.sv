module two_state_out #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output bit   [N-1:0] y
);
  assign y = a & b;
endmodule
