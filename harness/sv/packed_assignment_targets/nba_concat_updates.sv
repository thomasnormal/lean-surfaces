module top;
  logic [3:0] first, second;
  initial begin
    first = 4'b0000;
    second = 4'b0000;
    {first, second} <= 8'ha5;
    if (first !== 4'b0000 || second !== 4'b0000) begin
      $display("FAIL: whole concatenated NBA visible before commit");
      $finish;
    end
    {first[1:0], {second[3:2], second[1:0]}} <= 6'b100111;
    if (first !== 4'b0000 || second !== 4'b0000) begin
      $display("FAIL: nested concatenated NBA visible before commit");
      $finish;
    end
    {first[3:1], first[2:0]} <= 6'b101111;
    if (first !== 4'b0000) begin
      $display("FAIL: overlapping concatenated NBA visible before commit");
      $finish;
    end
    $display("PASS");
    $finish;
  end
endmodule
// REFERENCE: 040db5a3b0f6e7329320cf1b xrun(64) 24.03-s004 2026-10-11T13:06:56Z
