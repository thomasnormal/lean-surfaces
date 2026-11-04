module top;
  int count,value;
  initial begin
    count=0;
    value=(count++:7:count++);
    $display("unselected %0d %0d",value,count);
    $finish;
  end
endmodule
