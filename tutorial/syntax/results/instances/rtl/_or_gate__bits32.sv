module _or_gate__bits32 (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] c
);

    // module parameters:
    // bits = 32 (int)

    assign c = a | b;

endmodule
