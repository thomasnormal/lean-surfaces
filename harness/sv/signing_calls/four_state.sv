module top;
  logic [3:0] value_x, value_z;
  logic [7:0] signed_x, signed_z, unsigned_x, unsigned_z;
  bit [7:0] squashed;

  initial begin
    value_x = 4'bx01z;
    value_z = 4'bz10x;
    signed_x = $signed(value_x);
    signed_z = $signed(value_z);
    unsigned_x = $unsigned(value_x);
    unsigned_z = $unsigned(value_z);
    squashed = $signed(value_x);
    if ((signed_x === 8'bxxxxx01z) && (signed_z === 8'bzzzzz10x) &&
        (unsigned_x === 8'b0000x01z) && (unsigned_z === 8'b0000z10x) &&
        (squashed === 8'b00000010) &&
        ($unsigned($signed(value_x)) === value_x) &&
        ($signed($unsigned(value_z)) === value_z) &&
        $isunknown($signed(value_x)) && $isunknown($unsigned(value_z)))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 03623b26f8d8f8a7fa2b46f7 independent-simulator 2026-10-11T16:22:53Z
