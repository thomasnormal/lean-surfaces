module top;
 int i,y,z;
 let twice(a)=a+a;
 let unused(a)=42;
 let both(a,b)=a&&b;
 initial begin
   i=2; y=twice(i++);
   $display("repeat %0d %0d",i,y);
   z=unused(i++);
   $display("unused %0d %0d",i,z);
   y=both(0,i++);
   $display("short %0d %0d",i,y);
   $finish;
 end
endmodule
