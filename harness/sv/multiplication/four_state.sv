module top;
  logic [3:0] unknown_value, zero_value, known_value, product;
  logic [7:0] wide;
  bit [3:0] two_state;

  initial begin
    unknown_value = 4'b0x10;
    zero_value = 4'b0000;
    known_value = 4'b0011;
    product = zero_value * unknown_value;
    wide = known_value * unknown_value;
    two_state = known_value * unknown_value;
    if ((product !== 4'bxxxx) || (wide !== 8'bxxxxxxxx) ||
        (two_state !== 4'b0000))
      $display("FAIL");
    else begin
      unknown_value = 4'b01z0;
      product = unknown_value * known_value;
      if (product === 4'bxxxx)
        $display("PASS");
      else
        $display("FAIL");
    end
    $finish;
  end
endmodule
// REFERENCE: ee07aad473a5d501dbc98ed1 independent-simulator 2026-10-11T18:11:29Z
