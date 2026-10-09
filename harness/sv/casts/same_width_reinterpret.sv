module top;
  logic [31:0] unsigned_word;
  logic signed [63:0] signed_word;
  integer signed_result;
  time unsigned_result;

  initial begin
    unsigned_word = 32'h80000001;
    signed_word = 64'h8000000000000001;
    signed_result = integer'(unsigned_word);
    unsigned_result = time'(signed_word);
    $display("reinterpret=[%h][%h]", signed_result, unsigned_result);
    if ((signed_result === 32'h80000001) &&
        (unsigned_result === 64'h8000000000000001) &&
        (integer'(unsigned_word) < 0) && !(unsigned_word < 0) &&
        (signed_word < 0) && !(time'(signed_word) < 0))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 0686ed9f68444327eda04831 TOOL:	xrun(64)	24.03-s004 2026-10-09T21:34:32Z
