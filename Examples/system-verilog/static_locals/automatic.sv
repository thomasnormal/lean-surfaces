module automatic top;
 int source,result;
 initial begin
  source=2;
  repeat(3) begin
   automatic int fresh=source;
   static int count=0;
   #1;count++;fresh++;
   result=fresh;source=source+3;
   $display("automatic %0d %0d",count,result);
  end
  $finish;
 end
endmodule
