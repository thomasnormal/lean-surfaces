/*
:name: packed_struct
:description: §7.2 — direct packed-struct field assignment and read
:tags: 7.2
:type: simulation
*/
module top;
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } word_t;
  word_t value;
  initial begin
    value.hi = 4'ha;
    if (value.hi === 4'ha) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
