module top;
 int i,y;
 let unused(a)=42;
 initial begin
  i=5;y=unused(i++);
  $display("unused %0d %0d",i,y);
  $finish;
 end
endmodule
