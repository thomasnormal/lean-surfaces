module top;
  for (genvar i=0; i<2; i++) begin : workers
    int value;
    initial value = #2 i+30;
  end
  initial begin
    #1;
    $display("pending %0d %0d", workers[0].value, workers[1].value);
    #2;
    $display("captured %0d %0d", workers[0].value, workers[1].value);
    $finish;
  end
endmodule
