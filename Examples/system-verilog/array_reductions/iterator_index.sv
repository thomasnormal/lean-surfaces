module top;
  int cells[3:1]='{2,4,8};
  initial begin
    $display("index %0d",cells.sum(x) with (x+x.index));
    $finish;
  end
endmodule
