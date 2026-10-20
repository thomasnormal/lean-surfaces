module top;
  logic [3:0] cells[1:0];
  logic [3:0] result;
  initial begin
    cells='{4'd15,4'd2};
    result=cells.sum();
    $display("certificate %0d",result);
    $finish;
  end
endmodule
