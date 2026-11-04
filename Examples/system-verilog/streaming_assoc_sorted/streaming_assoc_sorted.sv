/*
:name: streaming_assoc_sorted
:description: IEEE 1800-2023 §11.4.14.1 finite integral associative arrays stream in sorted index order
:tags: 7.9 11.4.14.1 associative array streaming
:type: simulation
*/
module top;
  int values[int];
  bit [95:0] stream;
  initial begin
    values[3] = 32'hCCCC_CCCC;
    values[1] = 32'hAAAA_AAAA;
    values[2] = 32'hBBBB_BBBB;
    stream = {>> {values}};
    if (stream[95:64] === 32'hAAAA_AAAA &&
        stream[63:32] === 32'hBBBB_BBBB &&
        stream[31:0] === 32'hCCCC_CCCC)
      $display("PASS");
    else
      $display("FAIL %h", stream);
    $finish;
  end
endmodule
