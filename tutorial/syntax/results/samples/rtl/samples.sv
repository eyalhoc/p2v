module samples (
    input logic clk0,
    input logic clk0_rst_n,
    input logic clk1,
    input logic clk1_reset,
    input logic ext_reset,
    input logic valid,
    input logic [7:0] i0,
    output logic [7:0] x0,
    output logic [7:0] x1,
    output logic [7:0] x2,
    output logic [7:0] x3,
    output logic [7:0] x4,
    input logic [7:0] s__ctrl,
    input logic [31:0] s__data,
    input logic s__valid,
    output logic s__ready,
    output logic [7:0] t__ctrl,
    output logic [31:0] t__data,
    output logic t__valid,
    input logic t__ready
);


    always_ff @(posedge clk0 or negedge clk0_rst_n)
        if (!clk0_rst_n) x0 <= 8'd0;
        else x0 <= i0;

    always_ff @(posedge clk1)
        if (clk1_reset) x1 <= 8'd0;
        else x1 <= i0;

    always_ff @(posedge clk0 or negedge clk0_rst_n)
        if (!clk0_rst_n) x2 <= 8'd0;
        else if (valid) x2 <= i0;

    always_ff @(posedge clk0 or negedge clk0_rst_n)
        if (!clk0_rst_n) x3 <= {8{1'b1}};
        else if (valid) x3 <= i0;

    always_ff @(posedge clk0 or negedge clk0_rst_n)
        if (!clk0_rst_n) x4 <= 8'd0;
        else if (ext_reset) x4 <= 8'd0;
        else if (valid) x4 <= i0;

    always_ff @(posedge clk1)
        if (clk1_reset) t__ctrl <= 8'd0;
        else if (valid) t__ctrl <= (s__ctrl | 8'h04);


    assign s__ready = t__ready;
    always_ff @(posedge clk1)
        if (clk1_reset) t__valid <= 1'd0;
        else if (~t__valid | ~s__ready) t__valid <= s__valid;



    always_ff @(posedge clk1)
        if (clk1_reset) t__data <= 32'd0;
        else if ((s__valid & s__ready)) t__data <= s__data;



endmodule  // samples
