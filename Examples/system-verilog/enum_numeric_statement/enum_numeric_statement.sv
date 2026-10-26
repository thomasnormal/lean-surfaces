/* Discarded numeric enum methods are pure reads of the current enum value. */
module top;
  typedef enum logic [1:0] { A = 0, B = 1, C = 2 } E;
  E value;
  initial begin
    value = B;
    value.first();
    value.last();
    value.num();
    value.next();
    value.prev();
    $display("PASS");
    $finish;
  end
endmodule
