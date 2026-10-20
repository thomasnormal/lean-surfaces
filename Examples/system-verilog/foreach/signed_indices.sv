// IEEE 1800-2023 11.5.1 and 12.7.3: declared labels and runtime offsets.
module top;
  logic [-1:-3] negative_word=3'b1xz;
  logic [1:3] ascending_word=3'bz10;
  int index;
  initial begin
    foreach(negative_word[index])
      $display("negative %0d %b",index,negative_word[index]);
    foreach(ascending_word[index])
      $display("positive %0d %b",index,ascending_word[index]);
    index=32'h80000000;
    $display("minimum %b %b",negative_word[index],ascending_word[index]);
    index=32'h7fffffff;
    $display("maximum %b %b",negative_word[index],ascending_word[index]);
    index='x;
    $display("unknown %b %b",negative_word[index],ascending_word[index]);
    $finish;
  end
endmodule
