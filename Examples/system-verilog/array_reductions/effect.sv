module top;
  int cells[3]='{1,2,3};
  int count,result;
  initial begin
    count=0;
    result=cells.sum(x) with (x+count++);
    $display("effect %0d %0d",result,count);
    $finish;
  end
endmodule
