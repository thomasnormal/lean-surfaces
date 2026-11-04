package Values;
  parameter int BASE = 7;
endpackage
module top;
  for (genvar i=0; i<2; i++) begin : rows
    import Values::*;
    typedef logic [3:0] word_t;
    word_t cells[0:1] = '{BASE+i, BASE+i+1};
    initial cells[0] = i+2;
  end
  initial begin
    #1;
    $display("cells %h %h %h %h", rows[0].cells[0], rows[0].cells[1], rows[1].cells[0], rows[1].cells[1]);
    $finish;
  end
endmodule
