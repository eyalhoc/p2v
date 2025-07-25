module adder__bits8_num4 (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [7:0] data_in0,
    input logic [7:0] data_in1,
    input logic [7:0] data_in2,
    input logic [7:0] data_in3,
    output logic [7:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 8 (int) #  data width
    //  * num = 4 (int) #  number of inputs

    logic [7:0] data_out0;
    logic valid_out0;
    adder__bits8_num2 adder0 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in0(data_in0),  // input
        .data_in1(data_in1),  // input
        .o(data_out0),  // output
        .valid_out(valid_out0)  // output
    );

    logic [7:0] data_out1;
    logic valid_out1;
    adder__bits8_num2 adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in0(data_in2),  // input
        .data_in1(data_in3),  // input
        .o(data_out1),  // output
        .valid_out(valid_out1)  // output
    );

    adder__bits8_num2 adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valid_out0 & valid_out1)),  // input
        .data_in0(data_out0),  // input
        .data_in1(data_out1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits8_num4
