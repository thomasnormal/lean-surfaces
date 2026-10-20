package p;
 int held=4;
 let from_package(a)=held+a;
endpackage
let from_unit(a)=a*3;
module leaf;
 int x;
 let local_value(a)=a+x;
 initial x=5;
endmodule
module top;
 import p::*;
 leaf left(); leaf right();
 int answer;
 if(1) begin : g
   let nested(a)=from_package(a)+from_unit(a);
   initial begin
     answer=nested(2);
     #1;
     $display("structure %0d %0d %0d",answer,left.x,right.x);
     held=9; $display("live %0d",nested(2));
     $finish;
   end
 end
endmodule
