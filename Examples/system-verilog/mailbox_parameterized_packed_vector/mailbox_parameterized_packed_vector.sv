/*
:name: mailbox_parameterized_packed_vector
:description: IEEE 1800-2023 15.4.9 - a parameterized mailbox may constrain messages to a packed vector type.
:tags: 15.4.9
:type: simulation
:spec: IEEE 1800-2023 15.4.9 permits a mailbox to be parameterized to limit the message type.
*/
module top;
  initial begin
    mailbox #(bit [7:0]) mbx;
    bit [7:0] got;
    int ok;

    mbx = new();
    ok = mbx.try_put(8'ha5);
    if (ok <= 0) begin
      $display("FAIL: try_put returned %0d", ok);
      $finish;
    end

    ok = mbx.try_get(got);
    if (ok > 0 && got === 8'ha5 && mbx.num() == 0)
      $display("PASS");
    else
      $display("FAIL: try_get=%0d got=0x%h num=%0d", ok, got, mbx.num());
    $finish;
  end
endmodule
