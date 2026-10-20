// SPDX-License-Identifier: Apache-2.0
// Common case type, live sets/ranges, ambiguity and first-match selection.
module top;
  logic signed [3:0] narrow = -1;
  logic signed [7:0] signed_item = -1;
  logic [3:0] subject = 4'bx001;
  logic [3:0] candidate = 4'b0001;
  logic [3:0] mask = 4'bz001;
  logic signed [64:0] wide_item = -1;
  logic signed [7:0] array_subject = -1;
  logic signed [7:0] signed_cells[2:0] = '{-1,2,3};
  logic [7:0] unsigned_cells[0:1] = '{15,2};
  int lo = -10;
  int hi = -1;
  int value = -3;
  int choice = 0;
  initial begin
    case(narrow) inside signed_item: choice=1; default: choice=2; endcase
    $display("signed %0d",choice);
    case(narrow) inside 8'hff: choice=3; default: choice=4; endcase
    $display("mixed %0d",choice);
    case(narrow) inside wide_item: choice=5; default: choice=6; endcase
    $display("wide %0d",choice);
    case(value) inside [lo:hi]: choice=7; [0:9]: choice=8; endcase
    $display("range %0d",choice);
    lo=4; hi=1; value=2;
    case(value) inside [lo:hi]: choice=9; default: choice=10; endcase
    $display("reversed %0d",choice);
    case(subject) inside candidate: choice=11; mask: choice=12; default: choice=13; endcase
    $display("dynamic %0d",choice);
    choice=14;
    case(subject) inside candidate: choice=15; [4'h0:4'hf]: choice=16; endcase
    $display("ambiguous %0d",choice);
    case(narrow) inside [4'sh8:4'sh0]: choice=17; [4'sh1:4'sh7]: choice=18; endcase
    $display("bounds %0d",choice);
    case(array_subject) inside signed_cells: choice=19; default: choice=20; endcase
    $display("signed_cells %0d",choice);
    case(array_subject) inside unsigned_cells: choice=21; default: choice=22; endcase
    $display("unsigned_cells %0d",choice);
    case(array_subject) inside signed_cells[1:0]: choice=23; default: choice=24; endcase
    $display("slice %0d",choice);
    subject=4'd5;
    case(subject) inside
      default: choice=25;
      [4'd1:4'd6],4'd9: begin
        case(subject) inside 4'd5: choice=26; default: choice=27; endcase
      end
      [4'd0:4'd15]: choice=28;
    endcase
    $display("first_nested %0d",choice);
    $finish;
  end
endmodule
