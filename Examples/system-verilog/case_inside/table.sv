// SPDX-License-Identifier: Apache-2.0
// All two-bit four-state subject/item pairs; only definite hits set a bit.
module top;
  logic [1:0] values[16] = '{2'b00,2'b01,2'b0x,2'b0z,
    2'b10,2'b11,2'b1x,2'b1z,2'bx0,2'bx1,2'bxx,2'bxz,
    2'bz0,2'bz1,2'bzx,2'bzz};
  logic [15:0] hits;
  int i,j;
  initial begin
    for(i=0;i<16;i++) begin
      hits=0;
      for(j=0;j<16;j++) begin
        case(values[i]) inside values[j]: hits[j]=1; endcase
      end
      $display("row %b %h",values[i],hits);
    end
    $finish;
  end
endmodule
