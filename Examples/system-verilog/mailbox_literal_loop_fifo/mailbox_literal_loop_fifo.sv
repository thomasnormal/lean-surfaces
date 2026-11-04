/* A finite literal mailbox FIFO replayed through two procedural loops. */
module top;
  mailbox #(int) mb = new();
  int v;
  int ok = 1;
  int val;
  initial begin
    for (int i = 0; i < 10; i++) begin
      val = i * 7;
      mb.put(val);
    end
    for (int i = 0; i < 10; i++) begin
      mb.get(v);
      if (v != i * 7) ok = 0;
    end
    if (ok == 1) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
