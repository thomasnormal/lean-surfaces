module top;
  for (genvar i=0; i<2; i++) begin : workers
    int result;
    initial begin
      automatic int local_value = i+10;
      automatic logic [3:0] cells[0:1] = '{i+1, i+2};
      #1;
      cells[0] = i+4;
      #1;
      result = local_value + cells[0] + cells[1];
    end
  end
  initial begin
    #3;
    $display("locals %0d %0d", workers[0].result, workers[1].result);
    $finish;
  end
endmodule
