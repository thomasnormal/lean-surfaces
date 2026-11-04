/*
:name: struct_decl_adapter
:description: An integral unpacked struct lowers to flat self-check cells.
:tags: 7.2 7.3
:type: simulation
*/
module top;
  typedef struct {
    int score;
    bit enabled;
  } record_t;

  initial begin
    record_t record;
    record.score = 42;
    record.enabled = 1;
    if (record.score == 42 && record.enabled)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
