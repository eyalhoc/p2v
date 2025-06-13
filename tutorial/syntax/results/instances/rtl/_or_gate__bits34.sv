module _or_gate__bits34 (
    input  logic [33:0] a,
    input  logic [33:0] b,
    output logic [33:0] c
);

    // module parameters:
    // bits = 34 (int)

    assign c = a | b;

endmodule
