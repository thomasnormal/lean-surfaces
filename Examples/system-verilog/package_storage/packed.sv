package Fields;
  typedef struct packed {logic [3:0] hi; logic [3:0] lo;} pair_t;
  pair_t word_value = 8'h96;
  logic [7:0] vector_value = 8'h12;
endpackage
module top;
  import Fields::word_value;
  initial begin
    $display("packed %h %h", word_value.hi, Fields::word_value.lo);
    word_value.lo = 4'hc;
    Fields::word_value.hi = 4'hd;
    Fields::vector_value[7:6] = 2'b11;
    $display("updated %h %h %h", Fields::word_value, word_value.hi, Fields::vector_value);
    $finish;
  end
endmodule
