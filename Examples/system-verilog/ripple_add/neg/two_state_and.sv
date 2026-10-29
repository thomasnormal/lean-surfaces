module two_state_and #(parameter int N = 4) (
  input  bit [N-1:0] a, b,
  output bit [N-1:0] y
);
  assign y = a & b;
endmodule
