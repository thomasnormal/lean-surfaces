// Enum-valued fixed-array cells retain their named type metadata and bit state.
module enum_fixed_array_element (
    output logic [1:0] out
);
  typedef enum logic [1:0] { A = 2'b00, B = 2'b01, C = 2'b10 } E;
  E arr [0:1];

  assign arr[0] = B;
  assign out = arr[0];
endmodule
