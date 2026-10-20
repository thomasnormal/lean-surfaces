module top;
 int a;
 function int f(input int x); return x+1; endfunction
 let apply(x)=f(x);
 initial begin a=apply(3);$display("call %0d",a);$finish;end
endmodule
