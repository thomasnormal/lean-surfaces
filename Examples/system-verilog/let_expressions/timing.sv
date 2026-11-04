module top;
 int a,b,result;
 let sum=a+b;
 initial begin
  a=3;b=4;result<=sum;
  a=10;#1;
  $display("captured %0d %0d",result,sum);
  #1; b=6;result=sum;
  $display("live-timing %0d",result);
  $finish;
 end
endmodule
