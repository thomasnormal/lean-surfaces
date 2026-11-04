/*
:name: mailbox_num_valid_only_until_next_operation
:description: §15.4.2 — num() returns the number of messages currently in the mailbox; the returned value is valid only until the next get() or put() is executed on the mailbox
:tags: 15.4.2
:type: simulation
*/
// IEEE 1800 §15.4.2: "The returned value should be used with care because it is valid
// only until the next get() or put() is executed on the mailbox."
// This test captures the snapshot nature of num(): the value returned reflects the count
// at the moment of the call, but a subsequent put() immediately changes the count.
// We verify that num() correctly reflects state at each call point.
module top;
  initial begin
    mailbox mbx;
    int cnt0, cnt1, cnt2, cnt3;
    int v;
    mbx = new();

    cnt0 = mbx.num();         // 0 messages
    mbx.put(10);
    cnt1 = mbx.num();         // 1 message (snapshotted here)
    mbx.put(20);              // count changes after the snapshot
    // cnt1 still holds value from before put(20) — demonstrates snapshot nature
    cnt2 = mbx.num();         // now 2 messages
    mbx.get(v);
    cnt3 = mbx.num();         // 1 message after get

    if (cnt0 == 0 && cnt1 == 1 && cnt2 == 2 && cnt3 == 1)
      $display("PASS");
    else
      $display("FAIL: cnt0=%0d cnt1=%0d cnt2=%0d cnt3=%0d (expected 0,1,2,1)",
               cnt0, cnt1, cnt2, cnt3);
    $finish;
  end
endmodule
