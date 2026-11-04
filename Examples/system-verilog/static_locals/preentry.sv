module top;
 initial begin
  #2;
  begin : late
   int count=6;
   logic [3:0] four=4'b1xz1;
   bit [3:0] two=4'b1xz1;
  end
 end
 initial begin
  $display("before %0d %b %b",late.count,late.four,late.two);
  #1;late.count=9;
  #2;$display("after %0d",late.count);$finish;
 end
endmodule
