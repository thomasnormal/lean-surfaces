// The binary XNOR operator `~^` and its spelling `^~` (IEEE 1800-2023 11.4.8, Table 11-14), WP-L2
// (2026-10-30). Both spellings are one slang operator (BinaryXnor); the extractor lowers it to
// `~(a ^ b)` (the two nodes the symbolic tier already has), so the 4-state table is the product of
// two pinned ones: any x/z operand bit gives x, else 1 when the bits are equal. One-bit and vector
// operands, a wider target (operands zero-extended to the context before the operator, so the
// extension bits are `0 ~^ 0 = 1`), an operand that is itself an expression, and a chain.
module xnor_bin #(parameter int N = 4) (
  input  logic [N-1:0] a, b, c,
  input  logic         p, q,
  output logic [N-1:0] y1,      // a ~^ b
  output logic [N-1:0] y2,      // a ^~ b
  output logic         z1,      // p ~^ q
  output logic [2*N-1:0] w,     // wider context: operands extended before the operator
  output logic [N-1:0] y3,      // (a & b) ~^ c: an operand that is an expression
  output logic [N-1:0] y4       // a ~^ b ~^ c: left-associative chain
);
  assign y1 = a ~^ b;
  assign y2 = a ^~ b;
  assign z1 = p ~^ q;
  assign w  = a ~^ b;
  assign y3 = (a & b) ~^ c;
  assign y4 = a ~^ b ~^ c;
endmodule
