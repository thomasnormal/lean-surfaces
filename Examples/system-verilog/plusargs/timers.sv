module top;
  timeunit 1ns;
  timeprecision 1ns;
  logic [15:0] word;
  int matched, index;
  initial begin
    word = 16'b10xz_xz10_zx01_01zx;
    index = 4;
    repeat (2) begin
      matched = $value$plusargs("BYTE=%h", word[index+:8]);
      $display("write %0d %b", matched, word);
      #1;
      word = 16'bz10x_zzzz_xxxx_xz10;
      matched = $value$plusargs("ABSENT=%h", word[index+:8]);
      $display("absent %0d %b", matched, word);
      #1;
    end
    $finish;
  end
endmodule
