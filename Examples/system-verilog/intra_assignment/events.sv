module top;
  timeunit 1ns;
  timeprecision 1ns;
  bit clk = 0;
  logic [7:0] source = 8'h10;
  logic [7:0] value;
  int count = 2;
  initial begin
    value = repeat(count) @(posedge clk) source;
    $display("repeated %h source %h count %0d",value,source,count);
    value = @(negedge clk) source;
    $display("single %h source %h",value,source);
    value = repeat(-2) @(posedge clk) source;
    $display("negative %h",value);
    value = repeat(32'bx) @(posedge clk) source;
    $display("unknown %h",value);
    $finish;
  end
  initial begin
    #1; source=8'h21; count=1; clk=1;
    #1; source=8'h32; clk=0;
    #1; source=8'h43; clk=1;
    #1; source=8'h54; clk=0;
  end
endmodule
