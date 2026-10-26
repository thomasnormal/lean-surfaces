/* A discarded enum.name() reads a modeled enum but has no state effect. */
module top;
  typedef enum logic [1:0] { A = 0, B = 1 } E;
  E value;
  initial begin
    value = B;
    value.name();
    $display("PASS");
    $finish;
  end
endmodule
