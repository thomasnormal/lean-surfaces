// Constant fixed-unpacked array cells reuse the symbolic vector store.
module fixed_array_element (
    input  logic source,
    output logic out
);
  logic [3:0] arr [0:1];

  assign arr[0] = {3'b000, source};
  assign out = arr[0][0];
endmodule
