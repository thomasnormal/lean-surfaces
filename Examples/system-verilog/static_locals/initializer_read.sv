module top;
 int source=4;
 initial begin
  begin : data
   static int saved=source;
  end
  $display("dependency %0d",data.saved);$finish;
 end
endmodule
