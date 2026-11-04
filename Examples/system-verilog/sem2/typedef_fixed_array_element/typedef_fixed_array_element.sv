// A packed integral typedef is erased while fixed array cells stay explicit.
module typedef_fixed_array_element (
    input  logic source,
    output logic out
);
  typedef logic [3:0] cell_t;
  cell_t arr [0:1];

  assign arr[0] = {3'b000, source};
  assign out = arr[0][0];
endmodule
