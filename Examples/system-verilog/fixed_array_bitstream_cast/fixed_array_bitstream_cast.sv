/*
:name: fixed_array_bitstream_cast
:description: §6.24.3 — an integral bit-stream cast fills fixed-array element 0 from the MSBs
:tags: 6.24.3
:type: simulation
*/
module top;
  typedef bit [23:0] bits_t;
  typedef bit [7:0] bytes_t [3];
  initial begin
    bits_t bits;
    bytes_t bytes;
    bits = 24'habcdef;
    bytes = bytes_t'(bits);
    if (bytes[0] === 8'hab && bytes[1] === 8'hcd && bytes[2] === 8'hef)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
