module signals #(
    parameter BITS = 32
) ();

    logic a;
    logic b;
    logic [7:0] c;
    logic [7:0] d;
    logic [7:0] e;
    logic [7:0] f0;
    logic [7:0] f1;
    logic [7:0] f2;
    logic [7:0] f3;
    logic [15:0] g;
    logic [15:0] h;
    logic clk;
    logic rst_n;
    logic clk2;
    logic clk2_rstn;
    assign clk   = 1'b1;
    assign rst_n = 1'b1;
    logic [BITS-1:0] z;
    assign z = '0;

    localparam IDLE = 2'd0;
    logic [1:0] iii;
    assign iii = IDLE;


    assign b = 1'b1;
    assign e = 8'd3;
    assign f0 = d | e;
    assign f1 = d | e;
    assign f2 = d | e;
    assign f3 = d | e;
    assign a = b;
    assign c = 8'd0;
    assign d = e + 8'd1;
    assign g = {f0, f1};
    assign h[7:0] = f2;
    assign h[15:8] = f3;

    assign clk2_rstn = 1'b1;

    assign clk2 = clk;
    logic [7:0] aa;
    assign aa = 8'hff;

    logic [7:0] bb;
    initial bb = 8'hff;


    logic [ 7:0] s__ctrl;
    logic [31:0] s__data;
    logic [ 7:0] t__ctrl;
    logic [31:0] t__data;

    assign t__ctrl = s__ctrl;
    assign t__data = s__data;

    logic [ 7:0] s1__ctrl;
    logic [31:0] s1__data;
    logic [ 7:0] t1__ctrl;
    logic [31:0] t1__data;
    assign t1__ctrl = d;

    assign t1__data = s1__data;


    logic [7:0] s2__ctrl;
    logic [31:0] s2__data;
    logic s2__valid;
    logic s2__ready;
    logic [7:0] t2__ctrl;
    logic [31:0] t2__data;
    logic t2__valid;
    logic t2__ready;

    assign t2__ctrl  = s2__ctrl;
    assign t2__data  = s2__data;
    assign t2__valid = s2__valid;
    assign s2__ready = t2__ready;


endmodule
