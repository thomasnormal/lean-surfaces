/* Discarded integral signing casts have no represented state effect. */
module top;
  logic [7:0] value;
  initial begin
    $signed(8'hff);
    $unsigned(value);
    $display("PASS");
    $finish;
  end
endmodule
