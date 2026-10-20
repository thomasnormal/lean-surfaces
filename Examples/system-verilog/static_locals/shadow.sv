module top;
 int x;
 initial begin
  x=2;
  begin : first
   int x=3;
   begin : inner
    int x=5;
    x=x+first.x;
    $display("inner %0d %0d %0d",top.x,first.x,x);
   end
  end
  first.x=9;
  $display("distinct %0d %0d %0d",x,first.x,first.inner.x);
  $finish;
 end
endmodule
