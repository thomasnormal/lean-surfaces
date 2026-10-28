/*
:name: packed_aggregate_copy
:description: §7.2 — blocking copies of packed structs and unions use vector state
:tags: 7.2, 10.4
:type: simulation
*/
module top;
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } word_t;
  typedef union packed {
    logic [7:0] raw;
    word_t word;
  } packet_t;

  word_t source;
  word_t copied;
  packet_t packet_source;
  packet_t packet_copy;

  initial begin
    source = '{4'ha, 4'h5};
    copied = source;
    packet_source.raw = 8'h3c;
    packet_copy = packet_source;
    if (copied.hi === 4'ha && copied.lo === 4'h5 &&
        packet_copy.raw === 8'h3c)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
