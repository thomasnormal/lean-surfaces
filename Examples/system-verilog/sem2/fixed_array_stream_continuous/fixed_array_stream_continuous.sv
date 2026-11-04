// A continuous right stream reuses fixed vector windows for array cells.
module fixed_array_stream_continuous (
    input  logic [4:0] source,
    output logic [3:0] hi,
    output logic       out
);
  logic [3:0] arr [0:1];

  assign {>> {arr[0], out}} = source;
  assign hi = arr[0];
endmodule
