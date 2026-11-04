// Fixed-width numeric enum methods retain declaration-order traversal.
module enum_methods_fixed (
  input logic [1:0] value,
  output logic [1:0] first_value,
  output logic [1:0] last_value,
  output logic [31:0] count_value,
  output logic [1:0] next_value,
  output logic [1:0] prev_value
);
  typedef enum bit [1:0] { A = 2'd0, B = 2'd2, C = 2'd3 } E;
  E state;

  assign state = E'(value);
  assign first_value = state.first();
  assign last_value = state.last();
  assign count_value = state.num();
  assign next_value = state.next();
  assign prev_value = state.prev();
endmodule
