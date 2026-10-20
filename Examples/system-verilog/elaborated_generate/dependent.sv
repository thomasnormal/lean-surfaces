module top;
  int source_value = 6;
  if (1) begin : live
    int value = source_value;
  end
  initial begin #1; $display("dependent %0d", live.value); $finish; end
endmodule
