module top;
  int values[-2:-1];
  logic signed index;
  logic[31:0] unknown_index;
  initial begin
    values='{10,20};
    index=-1; values[index]+=3;
    index=0; values[index]+=5;
    unknown_index='x; values[unknown_index]*=2;
    $display("indices %0d %0d",values[-2],values[-1]);
    $finish;
  end
endmodule
