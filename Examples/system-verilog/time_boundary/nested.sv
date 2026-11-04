// Restriction metadata survives nested expressions and block structure.
module top;
  logic enable;
  initial begin
    enable = 1;
    #2;
    if (enable) begin
      $display("nested %0d", $time + 64'd1);
    end
    $finish;
  end
endmodule
