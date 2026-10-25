/*
:name: streaming_with_clause_refs_previously_unpacked_var
:description: §11.4.14.4 — The with expression is evaluated immediately before its corresponding array is streamed; thus, the expression can refer to data that are unpacked by the same operator but before the array; here len is unpacked first, then payload uses with [0 +: len]
:tags: 11.4.14.4
:type: simulation
*/
module top;
  initial begin
    // Stream layout (big-endian / >> streaming):
    // [31:0]  = length field (int = 2)
    // [63:32] = payload[0] (8'hAA padded to 32 bits)
    // [95:64] = payload[1] (8'hBB padded to 32 bits)
    bit [95:0] stream;
    int len;
    int payload[];

    payload = new[4];
    payload[0] = 99; payload[1] = 99; payload[2] = 99; payload[3] = 99;
    len = 0;

    // Build stream: first 32 bits = length=2, then two 32-bit elements
    stream = {32'd2, 32'h000000AA, 32'h000000BB};

    // Unpack: len comes first (its with expression evaluated first),
    // then payload uses len (already unpacked) to decide its extent
    {>> {len, payload with [0 +: len]}} = stream;

    // len should be 2
    if (len !== 2)
      $display("FAIL: len=%0d (expected 2)", len);
    // payload[0..1] filled; payload[2..3] unchanged (99)
    else if (payload[0] === 32'h000000AA && payload[1] === 32'h000000BB &&
             payload[2] === 99 && payload[3] === 99)
      $display("PASS");
    else
      $display("FAIL: payload=%0d %0d %0d %0d", payload[0], payload[1], payload[2], payload[3]);

    $finish;
  end
endmodule
