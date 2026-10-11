module top;
  logic [7:0] left, right, product, precedence;
  logic [3:0] narrow;
  logic [15:0] wide;

  initial begin
    left = 8'd13;
    right = 8'd23;
    product = left * right;
    narrow = left * right;
    wide = left * right;
    precedence = left + right * 8'd2;
    if ((product === 8'h2b) && (narrow === 4'hb) &&
        (wide === 16'h012b) && (precedence === 8'h3b))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: b8d2a479db81e6eb478163a2 independent-simulator 2026-10-11T18:11:32Z
