module top;
  int values[0:1];
  int index;
  logic[7:0] unknown_value;
  initial begin
    values='{10,20}; index=5; unknown_value='x;
    values[index]+=$clog2(unknown_value);
    $display("unresolved %0d %0d",values[0],values[1]);
    $finish;
  end
endmodule
