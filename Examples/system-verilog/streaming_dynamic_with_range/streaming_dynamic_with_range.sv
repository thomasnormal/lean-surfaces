/*
:name: streaming_with_clause_unpack
:description: §11.4.14.4 — The with clause can specify unpack target extent; when used in unpack the specified array locations are filled and remainder unmodified
:tags: 11.4.14
:type: simulation
*/
module test;
  initial begin
    int payload[];
    int len;
    bit [63:0] stream;

    payload = new[4];
    payload[0] = 99; payload[1] = 99; payload[2] = 99; payload[3] = 99;
    len = 2;
    stream = 64'h0000_0001_0000_0002;  // element[0]=1, element[1]=2

    // Unpack only 2 elements into payload[0] and payload[1]
    {>> {payload with [0 +: len]}} = stream;
    // payload[0] should = 1, payload[1] should = 2, payload[2..3] unchanged (99)
    if (payload[0] === 1 && payload[1] === 2 && payload[2] === 99 && payload[3] === 99)
      $display("PASS");
    else
      $display("FAIL: %0d %0d %0d %0d", payload[0], payload[1], payload[2], payload[3]);
    $finish;
  end
endmodule
