module _or_gate__bits8 (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] c
);

    // module parameters:
    // bits = 8 (int)

    assign c = a | b;

endmodule
