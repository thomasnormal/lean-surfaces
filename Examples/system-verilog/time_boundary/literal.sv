// An ordinary zero literal has no clock restriction.
module top;
  initial begin
    #2;
    $display("literal %0d", 64'd0);
    $finish;
  end
endmodule
