program top;
 int a; let twice(x)=x+x;
 initial begin a=twice(3); $display("program %0d",a);$finish;end
endprogram
