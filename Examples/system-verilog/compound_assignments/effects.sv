module top;
  logic[7:0] data;
  int index;
  initial begin
    data=8'h1; index=0;
    data[index++]^=1'b1;
    data[0]+=index++;
    $display("effects %h %0d",data,index);
    $finish;
  end
endmodule
