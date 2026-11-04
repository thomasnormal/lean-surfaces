// IEEE 1800-2023 21.3.4.3: ordered outputs and partial copyback.
module top;
  logic [15:0] word;
  integer n, index;
  bit [7:0] clean;
  logic [31:0] input_bytes;
  logic [3:0] high; bit [3:0] low; logic [63:0] wide_count;
  initial begin
    word=16'hbeef;
    n=$sscanf("5 a", "%h %h", word[11:8], word[7:4]);
    $display("full %0d %h", n, word);
    n=$sscanf("3 q", "%h %h", word[11:8], word[7:4]);
    $display("partial %0d %h", n, word);
    n=$sscanf("q 7", "%h %h", word[11:8], word[7:4]);
    $display("zero %0d %h", n, word);
    index=4; word=16'hbeef;
    n=$sscanf("8 5", "%d %h", index, word[index+:4]);
    $display("ordered %0d %0d %h", n, index, word);
    n=99; n=$sscanf("12", "%d", n);
    $display("result_last %0d", n);
    word=16'habcd;
    word[3:0]=$sscanf("5", "%h", word[3:0]);
    $display("overlap %h", word);
    clean=8'hff; n=$sscanf("xz", "%h", clean);
    $display("two_state %0d %h", n, clean);
    input_bytes=32'h00410042;
    n=$sscanf(input_bytes, "%3c", word);
    $display("nul_characters %0d %h", n, word);
    input_bytes=32'h00313200;
    n=$sscanf(input_bytes, "%d", input_bytes);
    $display("input_once %0d %0d", n, input_bytes);
    wide_count=$sscanf("xz", "%h", {high, low});
    $display("concat %0d %h %h", wide_count, high, low);
    $finish;
  end
endmodule
