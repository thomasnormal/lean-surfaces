module top;
  logic [3:0] first, second;
  bit [1:0] two_state;
  logic [1:0] index;
  initial begin
    first = 4'b0000;
    second = 4'b0000;
    {first, second} = 8'ha5;
    if (first !== 4'ha || second !== 4'h5) begin
      $display("FAIL: whole concatenation destinations");
      $finish;
    end
    first = 4'b0000;
    second = 4'b0000;
    {first[1:0], {second[3:2], second[1:0]}} = 6'b100111;
    if (first !== 4'b0010 || second !== 4'b0111) begin
      $display("FAIL: nested selected concatenation destinations");
      $finish;
    end
    {two_state, first[1:0]} = 4'bxzz1;
    if (two_state !== 2'b00 || first !== 4'b00z1) begin
      $display("FAIL: per-destination two-state conversion");
      $finish;
    end
    {first, first} = 8'ha5;
    if (first !== 4'ha) begin
      $display("FAIL: reference alias assignment order");
      $finish;
    end
    first = 4'b0000;
    index = 2'b00;
    {index, first[index]} = 3'b111;
    if (index !== 2'b11 || first !== 4'b0001) begin
      $display("FAIL: reference live index order");
      $finish;
    end
    first = 4'b0000;
    index = 2'b00;
    {first[index], index} = 3'b111;
    if (index !== 2'b11 || first !== 4'b1000) begin
      $display("FAIL: reference index observes earlier destination write");
      $finish;
    end
    first = 4'ha;
    second = 4'h5;
    {first, second} = {second, first};
    if (first !== 4'h5 || second !== 4'ha) begin
      $display("FAIL: RHS is captured once before destination writes");
      $finish;
    end
    first = 4'b0000;
    {first[3:1], first[2:0]} = 6'b101111;
    if (first !== 4'b1011) begin
      $display("FAIL: overlapping selected destinations");
      $finish;
    end
    index = 2'bxx;
    {first[index], second[0]} = 2'b01;
    if (first !== 4'b1011 || second !== 4'b1011) begin
      $display("FAIL: unknown selected destination remains a no-op");
      $finish;
    end
    $display("PASS");
    $finish;
  end
endmodule
// REFERENCE: c69f913f6ab1ccc046e6c580 xrun(64) 24.03-s004 2026-10-10T13:41:26Z; PASS; observed right-to-left destination oracle.
