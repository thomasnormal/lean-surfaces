// Low chunks move first; a final short high chunk receives no internal padding.
module top;
  logic [7:0] source, bits_out, chunk3, chunk16;
  logic [9:0] short_source, chunk4;
  logic [11:0] wide;
  initial begin
    source = 8'b10xz0110;
    short_source = 10'b10xz011010;
    bits_out = {<< {source}};
    chunk3 = {<< 3 {source}};
    chunk16 = {<< 16 {source}};
    chunk4 = {<< 4 {short_source}};
    wide = {<< 3 {source}};
    $display("%b %b %b %b %b", bits_out, chunk3, chunk16, chunk4, wide);
    if (bits_out !== 8'b0110zx01 || chunk3 !== 8'b110xz010 ||
        chunk16 !== source || chunk4 !== 10'b1010xz0110 ||
        wide !== 12'b110xz0100000)
      $display("FAIL");
    else
      $display("PASS");
    $finish;
  end
endmodule
