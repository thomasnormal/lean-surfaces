/* A constant replication of a string literal has no represented state. */
module top;
  string value;
  initial begin
    value = {3{"x"}};
    $display("PASS");
    $finish;
  end
endmodule
