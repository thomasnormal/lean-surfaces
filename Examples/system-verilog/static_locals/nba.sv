module top;
 int result;
 initial begin
  #2;
  begin : data
   int value=5;
  end
 end
 initial begin
  result<=data.value;
  data.value=9;
  #1;$display("nba %0d %0d",result,data.value);
  #2;$display("stable %0d",data.value);$finish;
 end
endmodule
