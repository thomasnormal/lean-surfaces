module top;
  timeunit 1ns;
  timeprecision 1ns;
  logic [7:0] source = 8'bx10z10xz;
  logic [15:0] word = 16'b10xz_xz10_zx01_01zx;
  bit [3:0] clean;
  int index=0;
  initial begin
    source <= 9;
    {clean,word[3:0]} = #1 source;
    $display("concat %b %b source %0d",clean,word,source);
    repeat(3) begin
      word[index+:4] = #1 source[3:0];
      source++;
      index+=4;
    end
    $display("reentry %b %0d %0d",word,source,index);
    $finish;
  end
endmodule
