/* Equal-length fixed unpacked array assignment may read a wire-array source. */
module top;
  logic [7:0] value [0:1];
  wire  [7:0] source [0:1];

  assign source[0] = 8'h12;
  assign source[1] = 8'h34;

  initial begin
    value = source;
    if (value[0] === 8'h12 && value[1] === 8'h34)
      $display("PASS");
    else
      $display("FAIL %h %h", value[0], value[1]);
    $finish;
  end
endmodule
