module top;
 int source=2;
 initial begin
  repeat(2) begin
   automatic int fresh=source;
   static int count=0;
   #2;count++;
   $display("capture %0d %0d",count,fresh);
  end
  $finish;
 end
 initial begin #1;source=8;#2;source=12;end
endmodule
