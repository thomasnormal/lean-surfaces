/*
:name: mailbox_variable_fifo
:description: IEEE 1800-2023 §15.4.3 — a scalar variable with a pure literal write can be put into an unbounded mailbox FIFO
:tags: 15.4.3
:type: simulation
*/
module top;
  mailbox box;
  int first, second, third;
  int message;

  initial begin
    box = new();
    message = 100;
    box.put(42);
    box.put(10 + 5);
    box.put(message);
    box.get(first);
    box.get(second);
    box.get(third);
    if (first == 42 && second == 15 && third == 100)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
