module top;
  logic [15:0] word;
  logic [7:0] value;
  bit [7:0] clean;
  int count, result;
  initial begin
    $display("prefix %0d %0d %0d %0d", $test$plusargs("COUNT"),
      $test$plusargs("CO"), $test$plusargs("count"), $test$plusargs("COUNT=9"));
    count = 0;
    result = $value$plusargs("COUNT=%0d", count);
    $display("first %0d %0d", result, count);
    result = $value$plusargs("NEG=%d", count);
    $display("signed %0d %0d", result, count);
    value = 8'h5a;
    result = $value$plusargs("MASK=%B", value);
    $display("unknown %0d %b", result, value);
    result = $value$plusargs("OCT=%o", value);
    $display("octal %0d %h", result, value);
    result = $value$plusargs("HEX=%X", value);
    $display("hex %0d %h", result, value);
    result = $value$plusargs("MASK=%b", clean);
    $display("two_state %0d %b", result, clean);
    word = 16'b10xz_xz10_zx01_01zx;
    result = $value$plusargs("HEX=%h", word[11:4]);
    $display("selected %0d %b", result, word);
    result = $value$plusargs("ABSENT=%h", word[11:4]);
    $display("absent %0d %b", result, word);
    count = 0;
    if ($value$plusargs("NEG=%d", count) && count == -17)
      $display("ordered yes");
    else $display("ordered no");
    count = 77;
    if (0 && $value$plusargs("NEG=%d", count)) $display("unreachable");
    if (1 || $value$plusargs("NEG=%d", count)) $display("short %0d", count);
    count = 77;
    result = 1'bx && $value$plusargs("NEG=%d", count);
    $display("unknown_left %b %0d", result, count);
    count = 77;
    result = $value$plusargs("NEG=%d", count) || $value$plusargs("COUNT=%d", count);
    $display("left_write %0d %0d", result, count);
    $finish;
  end
endmodule
