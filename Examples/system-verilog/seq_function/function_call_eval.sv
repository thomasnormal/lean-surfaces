// Refused construct: a user-defined function call in a combinational expression.
// Refused by: run2 process evaluator.
// Exact message: unsupported expression 'CallExpression'
module function_call_eval(input logic [3:0] a, output logic [3:0] y);
  function automatic logic [3:0] step(input logic [3:0] x);
    step = x + 4'd1;
  endfunction
  assign y = step(a);
endmodule
