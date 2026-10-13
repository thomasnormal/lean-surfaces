module top;
  integer count, total;
  logic signed [3:0] signed_count;
  logic [3:0] unsigned_count;
  logic [3:0] unknown_count;
  logic [63:0] wide_count;
  initial begin
    total = 0;
    count = 3;
    repeat (count) begin
      count = 0;
      total += 1;
    end
    if (total !== 3) $display("FAIL count sampled once");
    total = 0;
    signed_count = -1;
    repeat (signed_count) total += 1;
    repeat (0) total += 1;
    if (total !== 0) $display("FAIL nonpositive count");
    total = 0;
    unknown_count = 4'bx001;
    repeat (unknown_count) total += 1;
    if (total !== 1) $display("FAIL unknown count conversion");
    total = 0;
    unknown_count = 4'bxxxx;
    repeat (unknown_count) total += 1;
    if (total !== 0) $display("FAIL all-unknown count conversion");
    unsigned_count = 15;
    repeat (unsigned_count) total += 1;
    if (total !== 15) $display("FAIL unsigned count");
    total = 0;
    wide_count = 64'd3;
    repeat (wide_count) begin
      total += 1;
      if (total == 2) break;
    end
    if (total !== 2) $display("FAIL wide count");
    total = 0;
    wide_count = 64'h00000000ffffffff;
    repeat (wide_count) begin
      total += 1;
      if (total > 1) break;
    end
    if (total !== 0) $display("FAIL signed-32 count conversion");
    $display("PASS");
    $finish;
  end
// REFERENCE: 7acd199fdc864881cd819a59 independent-simulator-24.03-s004 2026-10-13T02:50:52Z
endmodule
