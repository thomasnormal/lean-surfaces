// IEEE 1800-2023 6.19: bound enum and typedef aliases across lexical scopes.
typedef enum {UNIT_FIRST = 2, UNIT_SECOND} unit_t;
module top;
  typedef unit_t module_t;
  typedef module_t module_alias_t;
  module_alias_t global_state;
  initial begin
    typedef enum bit [2:0] {LOCAL_FIRST = 5, LOCAL_SECOND} local_t;
    typedef local_t local_alias_t;
    local_alias_t local_state;
    global_state = UNIT_SECOND;
    local_state = LOCAL_SECOND;
    if (global_state == 3 && local_state == 6 && UNIT_FIRST == 2 && LOCAL_FIRST == 5)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 24a98b281e507458e8d72f73 xrun(64) 24.03-s004 2026-10-09T23:17:01Z; PASS.
