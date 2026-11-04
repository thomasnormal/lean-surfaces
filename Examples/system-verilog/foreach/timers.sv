// IEEE 1800-2023 12.7.3: live array reads and retained tuple across delay.
module top;
  logic [4:2] descending_word;
  logic [1:3] ascending_word;
  int index=99;
  int visits=0;
  initial begin
    descending_word=3'b1xz;
    ascending_word=3'bz10;
    #4;
    descending_word=3'bz01;
  end
  initial begin
    #1;
    foreach(descending_word[index]) begin
      #2;
      visits++;
      $display("descending %0d %b %b",index,descending_word[index],descending_word);
    end
    foreach(ascending_word[index]) begin
      #1;
      $display("ascending %0d %b",index,ascending_word[index]);
    end
    $display("outer %0d visits %0d",index,visits);
    $finish;
  end
endmodule
