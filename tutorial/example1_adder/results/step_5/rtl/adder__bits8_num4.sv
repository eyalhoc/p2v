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

    logic [7:0] datas0;
    logic [7:0] datas1;
    logic valids0;
    logic valids1;
    adder__bits8_num2 adder0 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in0(data_in0),  // input
        .data_in1(data_in1),  // input
        .o(datas0),  // output
        .valid_out(valids0)  // output
    );

    adder__bits8_num2 adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in0(data_in2),  // input
        .data_in1(data_in3),  // input
        .o(datas1),  // output
        .valid_out(valids1)  // output
    );

    adder__bits8_num2 adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valids0 & valids1)),  // input
        .data_in0(datas0),  // input
        .data_in1(datas1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits8_num4
