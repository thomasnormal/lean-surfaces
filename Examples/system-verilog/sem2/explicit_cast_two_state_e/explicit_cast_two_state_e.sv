// IEEE 1800-2023 §6.24.1: size cast keeps the two-state operand class.
module explicit_cast_two_state_e #(parameter int W=8) (input bit [3:0] x, output logic [W-1:0] y);
  assign y = W'(x);
endmodule
