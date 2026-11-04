module top;
 int x,y;
 initial begin
  let plus(a)=a+x;
  let nested(a,b)=plus(a)*b;
  x=3;y=nested(4,2);
  $display("local %0d",y);
  x=8;y=nested(.b(3),.a(4));
  $display("live-local %0d",y);
  $finish;
 end
endmodule
