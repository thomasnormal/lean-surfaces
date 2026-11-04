// Xcelium matrix witness: qualified if, synthesis case attributes, and an
// explicit four-state don't-care default.  The attributes have no simulation
// meaning; they are retained here so the pinned row proves that fact.
module xcelium_qualified_ops (
  input  logic [1:0] a,
  output logic [1:0] qcase,
  output logic [1:0] qif,
  output logic [1:0] pif,
  output logic [1:0] attrs,
  output logic [1:0] xdefault
);
  always_comb begin
    qcase = 2'b00;
    unique case (a)
      2'b00: qcase = 2'b01;
      default: qcase = 2'b10;
    endcase

    qif = 2'b00;
    unique if (a == 2'b00) qif = 2'b01;
    else if (a == 2'b01) qif = 2'b10;
    else qif = 2'b11;

    pif = 2'b00;
    priority if (a == 2'b00) pif = 2'b01;
    else pif = 2'b10;

    attrs = 2'b00;
    (* full_case, parallel_case *) case (a)
      2'b00: attrs = 2'b01;
      default: attrs = 2'b10;
    endcase

    xdefault = 2'b00;
    case (a)
      2'b00: xdefault = 2'b01;
      default: xdefault = 2'bxx;
    endcase
  end
endmodule
