module top;
  logic[15:0] word;
  int index;
  logic[31:0] unknown_index;
  initial begin
    word=16'h1234; index=4; word[index+:4]+=4'h3;
    word[index+:4]<<=1; index=3; word[index]^=1'b1;
    word[15:8]|=8'hc0;
    $display("windows %h",word);
    index=14; word[index+:4]^=4'hf;
    unknown_index='x; word[unknown_index+:4]+=4'h1;
    index=-2; word[index+:4]|=4'hf;
    $display("clipped %h",word);
    $finish;
  end
endmodule
