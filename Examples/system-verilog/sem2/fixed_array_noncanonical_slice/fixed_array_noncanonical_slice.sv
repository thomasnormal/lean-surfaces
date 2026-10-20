// Constant packed slices inside fixed array cells retain declaration labels.
module fixed_array_noncanonical_slice (
    input  logic [1:0] source,
    output logic [3:0] out
);
  logic [10:7] arr [0:1];

  assign arr[0][10:9] = source;
  assign out = arr[0];
endmodule
