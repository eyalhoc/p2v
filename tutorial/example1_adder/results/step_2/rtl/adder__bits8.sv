module adder__bits8 (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] o
);

    // adder module parameters:
    //  * bits = 8 (int) #  data width

    assign o = (a + b);

endmodule
