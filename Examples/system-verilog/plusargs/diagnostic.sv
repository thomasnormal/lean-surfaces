module top;
  logic [7:0] value = 8'h5a;
  int result;
  initial begin
    result=$value$plusargs("BAD=%d",value);
    $display("conversion %0d %b",result,value);
    $finish;
  end
endmodule
