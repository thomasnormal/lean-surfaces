/*
:name: struct_array_field_default
:description: §7.2/10.9.2 — struct default keys recursively fill finite unpacked array fields
:tags: 7.2 10.9.2 unpacked-struct fixed-array default assignment-pattern
:type: simulation
*/
module top;
  typedef struct {
    int header;
    int payload [0:2];
  } packet_t;
  packet_t packet;

  initial begin
    packet = '{default: 7};
    if (packet.header == 7 && packet.payload[0] == 7 &&
        packet.payload[1] == 7 && packet.payload[2] == 7)
      $display("DEFAULT PASS");
    else
      $display("DEFAULT FAIL");

    packet = '{header: 12, default: 3};
    if (packet.header == 12 && packet.payload[0] == 3 &&
        packet.payload[1] == 3 && packet.payload[2] == 3)
      $display("KEYED PASS");
    else
      $display("KEYED FAIL");
    $finish;
  end
endmodule
