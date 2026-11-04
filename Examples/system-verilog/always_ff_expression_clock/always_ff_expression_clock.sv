// SPDX-License-Identifier: Apache-2.0
// always_ff clocks may be packed expressions; edge detection uses the result LSB.
module top;
  logic [1:0] bus;
  logic d;
  logic q_vector;
  logic q_selected;

  always_ff @(posedge bus)
    q_vector <= d;

  always_ff @(posedge bus[1])
    q_selected <= d;

  initial begin
    bus = 2'b00;
    d = 1'b1;
    #1;
    bus = 2'b10;
    #1;
    bus = 2'b11;
    #1;
    if (q_vector === 1'b1 && q_selected === 1'b1)
      $display("ALWAYS FF EXPRESSION CLOCK PASS");
    else
      $display("ALWAYS FF EXPRESSION CLOCK FAIL");
    $finish;
  end
endmodule
