// Reversed unpacked ranges retain their declared cell labels.
module fixed_array_reverse_range (
    input  logic source,
    output logic out
);
  logic [3:0] arr [1:0];

  assign arr[0] = {3'b000, source};
  assign out = arr[0][0];
endmodule
