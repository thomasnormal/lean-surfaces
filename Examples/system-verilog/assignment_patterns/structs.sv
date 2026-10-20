module top;
  typedef logic [3:0] nibble;
  typedef struct packed { nibble a; nibble b; logic [7:0] c; } record_t;
  typedef struct packed { record_t head; logic [3:0] tail; } nested_t;
  record_t typed = '{nibble:4'h3, c:8'ha5, b:4'h9};
  nested_t nested = '{head:'{a:4'h1, b:4'h2, c:8'h34}, tail:4'h5};
  typedef struct packed signed { logic signed [3:0] a; logic [3:0] b; } signed_t;
  signed_t negative = '{4'hf, 4'he};
  bit [3:0] clean = '{1'b1, 1'bx, 1'bz, 1'b1};
  initial begin
    $display("structs %h %h %0d %b", typed, nested, negative, clean);
    $finish;
  end
endmodule
