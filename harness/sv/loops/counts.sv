module top;
  integer count, total;
  logic signed [3:0] signed_count;
  logic [3:0] unsigned_count;
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
    $display("PASS");
    $finish;
  end
// REFERENCE: d7fae9a22fd79e2cc27aa6ca independent-simulator 2026-10-12T11:59:51Z
endmodule
