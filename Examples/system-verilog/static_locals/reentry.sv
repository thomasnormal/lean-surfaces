module top;
 initial begin
  repeat(3) begin : frame
   static int saved=4;
   automatic int fresh=4;
   saved++;fresh++;
   $display("entry %0d %0d",saved,fresh);
   #1;
  end
  $display("retained %0d",frame.saved);
  $finish;
 end
endmodule
