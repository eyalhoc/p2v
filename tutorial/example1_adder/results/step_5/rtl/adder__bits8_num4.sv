module adder__bits8_num4 (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [7:0] i0,
    input logic [7:0] i1,
    input logic [7:0] i2,
    input logic [7:0] i3,
    output logic [7:0] o,
    output logic valid_out
);

    // module parameters:
    // clk = clk (p2v_clock)
    // bits = 8 (int): data width
    // num = 4 (int): number of inputs

    logic [7:0] o0;
    logic valid_out0;
    adder__bits8_num2 adder0 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .i0(i0),  // input
        .i1(i1),  // input
        .o(o0),  // output
        .valid_out(valid_out0)  // output
    );

    logic [7:0] o1;
    logic valid_out1;
    adder__bits8_num2 adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .i0(i2),  // input
        .i1(i3),  // input
        .o(o1),  // output
        .valid_out(valid_out1)  // output
    );

    adder__bits8_num2 adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid_out0 & valid_out1),  // input
        .i0(o0),  // input
        .i1(o1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule
