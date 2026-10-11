module top;
  logic [7:0] product, factor;
  logic signed [3:0] signed_product, signed_factor;

  initial begin
    product = 8'd13;
    factor = 8'd23;
    product *= factor;
    signed_product = -4'sd7;
    signed_factor = 4'sd3;
    signed_product *= signed_factor;
    if ((product === 8'h2b) && (signed_product === 4'hb))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 3d9fd8f60b587670e977c30a independent-simulator 2026-10-11T18:11:26Z
