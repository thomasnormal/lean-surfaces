module xsel (input  logic sel,
             input  logic [7:0] a, b,
             output logic [7:0] y);
  always_comb
    if (sel) y = a;
    else     y = b;
endmodule
