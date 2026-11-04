/*
:name: mailbox_literal_peek
:description: IEEE 1800-2023 §15.4.5 — peek and try_peek preserve FIFO state
:tags: 15.4.5
:type: simulation
*/
module top;
  mailbox box;
  int first, second, peeked, remaining;

  initial begin
    box = new();
    box.put(10);
    box.put(20);
    box.peek(first);
    box.get(second);
    box.try_peek(peeked);
    remaining = box.num();
    if (first == 10 && second == 10 && peeked == 20 && remaining == 1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
