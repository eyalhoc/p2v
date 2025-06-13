module _or_gate__bits35 (
    input  logic [34:0] a,
    input  logic [34:0] b,
    output logic [34:0] c
);

    // module parameters:
    // bits = 35 (int)

    assign c = a | b;

endmodule
