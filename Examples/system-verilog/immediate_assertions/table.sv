// SPDX-License-Identifier: Apache-2.0
module top;
  logic [1:0] patterns[0:15] = '{2'b00,2'b01,2'b0x,2'b0z,
    2'b10,2'b11,2'b1x,2'b1z,2'bx0,2'bx1,2'bxx,2'bxz,
    2'bz0,2'bz1,2'bzx,2'bzz};
  logic [1:0] gate;
  int i;
  int asserted;
  int assumed;
  int covered;
  initial begin
    for (i=0; i<16; i++) begin
      gate = patterns[i];
      asserted=0; assumed=0; covered=0;
      assert (gate) asserted=1; else asserted=2;
      assume (gate) assumed=1; else assumed=2;
      cover (gate) covered=1;
      $display("row %b %0d %0d %0d",gate,asserted,assumed,covered);
    end
    $finish;
  end
endmodule
