/* A discarded constant $clog2 query has no represented state effect. */
module top;
  parameter int WIDTH = 8;
  initial begin
    $clog2(8);
    $clog2(WIDTH);
    $display("PASS");
    $finish;
  end
endmodule
