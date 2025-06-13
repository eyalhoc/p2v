module adder (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] o
);

    assign o = a + b;

endmodule
