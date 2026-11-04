/*
:name: mailbox_typed_fifo
:description: IEEE 1800-2023 §15.4.3/15.4.5/26.7 — a typed mailbox#(int) has the same scalar FIFO behavior for matching messages
:tags: 15.4.3 15.4.5 26.7
:type: simulation
*/
module top;
  initial begin
    mailbox #(int) box = new();
    int first, second, remaining;
    box.put(10);
    box.put(20 + 1);
    box.get(first);
    remaining = box.num();
    box.get(second);
    if (first == 10 && second == 21 && remaining == 1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
