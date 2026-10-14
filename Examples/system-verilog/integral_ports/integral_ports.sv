module integral_ports(
  input bit [3:0] unsigned_bits,
  input bit signed [3:0] signed_bits,
  input int signed_integer,
  input integer four_state_integer,
  output bit [3:0] copied,
  output logic [3:0] value,
  output logic negative,
  output logic [31:0] wide,
  output logic less
);
  assign copied = unsigned_bits;
  assign value = signed_bits;
  assign negative = signed_bits < 0;
  assign wide = signed_integer;
  assign less = signed_integer < four_state_integer;
endmodule
