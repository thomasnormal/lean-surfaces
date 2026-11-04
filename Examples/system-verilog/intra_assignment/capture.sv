module top;
  timeunit 1ns;
  timeprecision 1ns;
  logic [15:0] word = 16'b10xz_xz10_zx01_01zx;
  logic [7:0] source = 8'ha5;
  int index = 0;
  initial begin
    word[index+:8] = #3 source;
    $display("selected %b source %h index %0d",word,source,index);
    $finish;
  end
  initial begin
    #1;
    source=8'h3c;
    index=4;
    word=16'bz10x_zzzz_xxxx_xz10;
    $display("changed %b",word);
  end
endmodule
