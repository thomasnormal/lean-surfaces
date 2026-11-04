/*
:name: mailbox_literal_fifo
:description: IEEE 1800-2023 15.4.3/15.4.5 — literal scalar mailbox FIFO put/get
:tags: 15.4.3 15.4.5
:type: simulation
*/
module top;
  mailbox box;
  int first, second, remaining;

  initial begin
    box = new();
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
