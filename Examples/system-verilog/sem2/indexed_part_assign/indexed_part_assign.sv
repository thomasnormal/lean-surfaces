// Literal indexed part-selects normalize to fixed packed windows.
module indexed_part_assign (
    input  logic [3:0] source,
    output logic [7:0] value
);
  assign value[0 +: 4] = source;
  assign value[7 -: 4] = 4'ha;
endmodule
