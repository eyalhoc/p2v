module clocks (
    input logic clk,
    input logic rst_n,
    input logic [31:0] i0,
    output logic [31:0] o0,
    input logic clk0,
    input logic [31:0] i1,
    output logic [31:0] o1,
    input logic clk1,
    input logic clk1_rst_n,
    input logic [31:0] i2,
    output logic [31:0] o2,
    input logic clk2,
    input logic clk2_reset,
    input logic [31:0] i3,
    output logic [31:0] o3,
    input logic clk3,
    input logic clk3_rst_n,
    input logic clk3_reset,
    input logic [31:0] i4,
    output logic [31:0] o4
);

    // module parameters:
    // clk = p2v_clock.clk_arst() (p2v_clock)

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) o0 <= 32'd0;
        else o0 <= i0;

    always_ff @(posedge clk0) o1 <= i1;

    always_ff @(posedge clk1 or negedge clk1_rst_n)
        if (!clk1_rst_n) o2 <= 32'd0;
        else o2 <= i2;

    always_ff @(posedge clk2)
        if (clk2_reset) o3 <= 32'd0;
        else o3 <= i3;

    always_ff @(posedge clk3 or negedge clk3_rst_n)
        if (!clk3_rst_n) o4 <= 32'd0;
        else if (clk3_reset) o4 <= 32'd0;
        else o4 <= i4;


endmodule
