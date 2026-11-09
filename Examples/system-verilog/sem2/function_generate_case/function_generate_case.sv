// Refused construct: a generated assignment calls an automatic function with a local case temporary.
// Refused by: the SV process evaluator in run2.
// Exact message: unsupported expression 'CallExpression'.
module function_generate_case(input logic [19:0] a, output logic [19:0] y);
  function automatic logic [4:0] map5(input logic [4:0] x);
    logic [4:0] t;
    unique case (x)
      5'h00: t = 5'h1f;
      default: t = 5'h00;
    endcase
    return t;
  endfunction
  genvar i;
  generate for (i = 0; i < 4; i = i + 1) begin : g
    assign y[5*i +: 5] = map5(a[5*i +: 5]);
  end endgenerate
endmodule
