package Defaults;
  parameter int WIDTH = 4;
  localparam int OFFSET = 3;
  typedef logic [WIDTH-1:0] word_t;
  typedef enum logic [3:0] {FIRST = 2, LAST = 9} choice_t;
  word_t unknown_value;
  bit [WIDTH-1:0] zero_value;
  bit [WIDTH-1:0] squashed = 4'b1xz0;
  int number = WIDTH + OFFSET;
endpackage
import Defaults::WIDTH;
module top;
  import Defaults::*;
  logic [WIDTH-1:0] local_value = LAST;
  initial begin
    $display("defaults %b %b %b number %0d", unknown_value, zero_value, squashed, number);
    $display("constants %0d %0d %b", Defaults::WIDTH, FIRST, local_value);
    $finish;
  end
endmodule
