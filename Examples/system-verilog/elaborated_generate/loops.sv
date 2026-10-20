module top;
  localparam int COUNT = 3;
  for (genvar i=0; i<COUNT; i++) begin : up
    int value = i*10;
    initial begin #2; value <= i*10+3; end
  end
  genvar j;
  for (j=2; j>=0; j--) begin : down
    int value = j+5;
    initial begin #1; value += 1; end
  end
  initial begin
    #3;
    $display("up %0d %0d %0d", up[0].value, up[1].value, up[2].value);
    $display("down %0d %0d %0d", down[0].value, down[1].value, down[2].value);
    $finish;
  end
endmodule
