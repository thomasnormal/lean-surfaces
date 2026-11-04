/*
:name: dynamic_array_continuous_target
:description: IEEE 1800-2023 §6.21 — a dynamic-array element is not a legal continuous-assignment destination; the invalid assignment is inert while the self-check body remains executable.
:tags: 6.21 assignment target dynamic array
:type: compile_error
:diagnostic_match: cannot refer to an element or member of a dynamic type outside of a procedural context
*/
module top;
  int dyn[];
  assign dyn[0] = 1;
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
