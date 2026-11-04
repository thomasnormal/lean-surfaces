/*
:name: sformat_constant_selected
:description: IEEE 1800-2023 Section 21.3.3 -- constant formatted writes to
  a fixed packed selection preserve surrounding bits.
:tags: 21.3.3 11.5.1
:type: simulation
*/
module top;
  logic [47:0] packet;
  initial begin
    packet = 'x;
    $sformat(packet[39:8], "%b", 4'b10xz);
    $sformat(packet[39:8], "%s:%0d", "Q", 2);
    $swrite(packet[39:8], "%0d", 5);
    $display("PASS");
    $finish;
  end
endmodule
