module top;
  localparam int VALUE = $clog2(8'hxx);
  initial begin
    $display("elaboration %0d", VALUE);
    $finish;
  end
endmodule
