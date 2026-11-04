/*
:name: multiple_variable_continuous_drivers
:description: IEEE 1800-2023 §10.3.2 — a variable may have at most one continuous assignment driver; an invalid group is inert while the self-check body remains executable.
:tags: 10.3.2 continuous assignment variable
:type: compile_error
:diagnostic_match: multiple continuous assignments to variable 'value'
*/
module top;
  logic a, b, value;
  assign value = a;
  assign value = b;
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
