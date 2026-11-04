module top;
  int values[2:-1];
  logic signed[7:0] lanes[0:1];
  int index;
  initial begin
    values='{3,7,11,15};
    index=1; values[index]+=35; values[index-1]*=2;
    lanes='{8'sh80,8'sh24}; index=0; lanes[index]>>>=2;
    index=1; lanes[index]<<<=1;
    $display("arrays %0d %0d %0d %0d %h %h",values[2],values[1],values[0],values[-1],lanes[0],lanes[1]);
    $finish;
  end
endmodule
