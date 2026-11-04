module top;
  logic[7:0] data;
  int index;
  initial begin
    data=8'ha5; index=1;
    data[index+:2]^=2'b11;
    $display("before %h",data);
    data<=8'h10;
    #1;
    index=4; data[index+:2]+=2'b10;
    $display("after %h",data);
    $finish;
  end
endmodule
