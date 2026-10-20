// A fixed array cell may be one leaf of a symbolic concatenation target.
module fixed_array_concat_target (
    input  logic [4:0] source,
    output logic [3:0] hi,
    output logic lo
);
  logic [3:0] arr [0:1];

  assign {arr[0], lo} = source;
  assign hi = arr[0];
endmodule
