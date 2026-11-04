/* A duplicate-free unique case that covers every value of its subject. */
module top;
  initial begin
    bit [1:0] a = 2'b01;
    int result = 0;
    unique case (a)
      2'b00: result = 0;
      2'b01: result = 1;
      2'b10: result = 2;
      2'b11: result = 3;
    endcase
    if (result === 1) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
