module adder (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] o
);

    // adder module parameters:

    assign o = (a + b);

endmodule
