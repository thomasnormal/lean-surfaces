/*
:name: streaming_with_range
:description: right streaming with a constant range updates only selected array cells
:tags: 11.4.14.4
:type: simulation
*/
module top;
  bit [63:0] source;
  int arr[4];
  initial begin
    source = 64'h0000_0001_0000_0002;
    arr[0] = 32'hff;
    arr[1] = 32'hff;
    arr[2] = 32'hff;
    arr[3] = 32'hff;
    {>> {arr with [0:1]}} = source;
    if (arr[0] === 1 && arr[1] === 2 &&
        arr[2] === 32'hff && arr[3] === 32'hff) $display("PASS");
    else $display("FAIL");
  end
endmodule
