module adder__bits35_num4 (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [34:0] data_in__0,
    input logic [34:0] data_in__1,
    input logic [34:0] data_in__2,
    input logic [34:0] data_in__3,
    output logic [34:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 35 (int) #  data width
    //  * num = 4 (int) #  number of inputs

    logic [34:0] datas__0;
    logic valids__0;
    adder__bits35_num2 adder0 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input // assumes port name equals wire name
        .data_in__0(data_in__0),  // input[34:0]
        .data_in__1(data_in__1),  // input[34:0]
        .o(datas__0),  // output[34:0]
        .valid_out(valids__0)  // output
    );

    logic [34:0] datas__1;
    logic valids__1;
    adder__bits35_num2 adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input // assumes port name equals wire name
        .data_in__0(data_in__2),  // input[34:0]
        .data_in__1(data_in__3),  // input[34:0]
        .o(datas__1),  // output[34:0]
        .valid_out(valids__1)  // output
    );

    adder__bits35_num2 adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valids__0 & valids__1)),  // input
        .data_in__0(datas__0),  // input[34:0]
        .data_in__1(datas__1),  // input[34:0]
        .o(o),  // output[34:0]
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits35_num4
