/*
:name: invalid_struct_replication_assignment
:description: IEEE 1800-2023 §5.10 — structure assignment patterns must not use replication.
:tags: 5.10 assignment pattern replication
:type: compile_error
:diagnostic_match: structure assignment pattern must not use replication
*/
module top;
  typedef struct { int x; int y; } pair_t;
  initial begin
    pair_t value;
    value = '{2{1}};
    $display("PASS");
    $finish;
  end
endmodule
