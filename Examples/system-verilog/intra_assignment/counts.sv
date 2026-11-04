module top;
  timeunit 1ns;
  timeprecision 1ns;
  bit clk=0;
  logic [7:0] source=8'h2a;
  logic [7:0] value=0;
  int count=-3;
  initial begin
    value=repeat(count) @(posedge clk) source;
    $display("negative %h",value);
    source=8'h35;
    value=repeat(0) @(posedge clk) source;
    $display("zero %h",value);
    source=8'h46;
    value=repeat(32'bx) @(posedge clk) source;
    $display("unknown_x %h",value);
    source=8'h57;
    value=repeat(32'bz) @(posedge clk) source;
    $display("unknown_z %h",value);
    count=2;
    value=repeat(count) @(posedge clk) source;
    $display("unreachable");
  end
  initial begin
    #1; count=0; source=8'h99;
    #1;
    $display("parked %h source %h count %0d",value,source,count);
    $finish;
  end
endmodule
