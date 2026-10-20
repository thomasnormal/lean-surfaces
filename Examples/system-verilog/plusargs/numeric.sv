module top;
  logic [3:0] narrow;
  logic [63:0] wide;
  logic [7:0] byte_value;
  int result;
  initial begin
    result=$value$plusargs("DEC=%d",narrow);
    $display("truncated %0d %h",result,narrow);
    result=$value$plusargs("SMALL=%d",wide);
    $display("padded %0d %h",result,wide);
    result=$value$plusargs("NEG=%d",byte_value);
    $display("negative %0d %h",result,byte_value);
    result=$value$plusargs("DSEP=%d",byte_value);
    $display("decimal_separators %0d %0d",result,byte_value);
    result=$value$plusargs("BSEP=%b",byte_value);
    $display("binary_separators %0d %b",result,byte_value);
    result=$value$plusargs("HSEP=%h",byte_value);
    $display("hex_separators %0d %h",result,byte_value);
    $finish;
  end
endmodule
