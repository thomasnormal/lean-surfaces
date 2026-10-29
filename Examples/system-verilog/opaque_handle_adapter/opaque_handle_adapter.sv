/*
:name: opaque_handle_adapter
:description: Uninitialized opaque class handles are metadata in both scopes.
:tags: 8 15
:type: simulation
*/
module top;
  mailbox module_box;
  semaphore module_sem;
  initial begin
    mailbox local_box;
    semaphore local_sem;
    $display("PASS");
    $finish;
  end
endmodule
