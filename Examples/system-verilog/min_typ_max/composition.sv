module top;
  logic[15:0] word;
  int shifted,condition,nested,replicated;
  logic relation;logic[7:0]concatenated;
  typedef struct packed{logic[3:0]hi;logic[3:0]lo;} pair_t;
  pair_t pattern_value;
  initial begin
    word={8'h11,8'h22};
    word[(0:4:8)+:4]+=(4'h1:4'h2:4'h3);
    shifted=1<<(1:2:3);
    condition=((0:1:0)?(10:20:30):(40:50:60));
    nested=((1:2:3):(4:5:6):(7:8:9));
    $display("composition %h %0d %0d %0d",word,shifted,condition,nested);
    relation=(1:3:5)<(2:2:2);
    concatenated={(4'h1:4'h2:4'h3),(4'ha:4'hb:4'hc)};
    pattern_value='{(4'h1:4'h2:4'h3),(4'h4:4'h5:4'h6)};
    replicated={(1:2:3){2'b10}};
    $display("relations %b concat %h",relation,concatenated);
    $display("patterns %h %h",pattern_value,replicated);
    $finish;
  end
endmodule
