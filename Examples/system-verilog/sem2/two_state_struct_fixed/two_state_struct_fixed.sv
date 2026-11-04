// A fixed packed struct made entirely of bit fields is one two-state vector.
module two_state_struct_fixed (
  input  logic [3:0] a,
  output logic [3:0] y
);
  typedef struct packed {
    bit [2:0] x;
    bit       z;
  } st_t;
  st_t s;
  assign s = a;
  assign y = s;
endmodule
