module top;
  timeunit 1ns;
  timeprecision 1ns;
  logic [7:0] source = 8'd5;
  logic [7:0] target = 0;
  logic [15:0] word = 16'b10xz_xz10_zx01_01zx;
  int index=0;
  initial begin
    target = #0 source;
    $display("inactive %0d %0d",target,source);
    #1;
    $display("committed %0d %0d",target,source);
    repeat(3) begin
      word[index+:4] = #1 source[3:0];
      source++;
      index+=4;
    end
    $display("reentry %b %0d %0d",word,source,index);
    $finish;
  end
  initial begin
    source <= 9;
    $display("active %0d",target);
  end
endmodule
