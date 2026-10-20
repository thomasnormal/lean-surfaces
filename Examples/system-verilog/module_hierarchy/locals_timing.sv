module leaf #(parameter int P=2);
  int value=0;
  initial begin
    int cursor;
    cursor=P;
    #1;
    cursor+=1;
    value<=cursor;
    #1;
    value+=cursor;
  end
endmodule
module top;
  leaf a(),b();
  initial begin
    int cursor;
    cursor=9;
    #3;
    $display("locals %0d %0d %0d",a.value,b.value,cursor);
    $finish;
  end
endmodule
