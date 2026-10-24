/*
:name: streaming_indexed_with_range
:description: right streaming with constant indexed with ranges selects fixed array cells
:tags: 11.4.14.4
:type: simulation
*/
module top;
  bit [95:0] source;
  bit [31:0] arr[8];

  initial begin
    // PLUS 255 255 1 2 3 255 255 255
    // MINUS 255 255 255 255 1 2 3 255
    source = {32'd1, 32'd2, 32'd3};
    arr[0] = 32'hff; arr[1] = 32'hff;
    arr[2] = 32'hff; arr[3] = 32'hff;
    arr[4] = 32'hff; arr[5] = 32'hff;
    arr[6] = 32'hff; arr[7] = 32'hff;

    {>> {arr with [2 +: 3]}} = source;
    $display("PLUS %0d %0d %0d %0d %0d %0d %0d %0d",
             arr[0], arr[1], arr[2], arr[3],
             arr[4], arr[5], arr[6], arr[7]);

    arr[0] = 32'hff; arr[1] = 32'hff;
    arr[2] = 32'hff; arr[3] = 32'hff;
    arr[4] = 32'hff; arr[5] = 32'hff;
    arr[6] = 32'hff; arr[7] = 32'hff;

    {>> {arr with [6 -: 3]}} = source;
    $display("MINUS %0d %0d %0d %0d %0d %0d %0d %0d",
             arr[0], arr[1], arr[2], arr[3],
             arr[4], arr[5], arr[6], arr[7]);
  end
endmodule
