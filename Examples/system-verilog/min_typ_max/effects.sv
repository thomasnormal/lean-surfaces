module top;
  int count,value;
  initial begin
    count=0;
    value=(count++:count++:count++);
    $display("effects %0d %0d",value,count);
    $finish;
  end
endmodule
