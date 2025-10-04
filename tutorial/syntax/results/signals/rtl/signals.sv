module signals #(
    parameter int BITS = 32
) (
    output logic [9:0] ccc,
    output logic [7:0] ccc2,
    input logic ext_clk,
    output logic [4:0] qq,
    output logic [7:0] master__0__w,
    output logic [7:0] master__0__r,
    output logic [7:0] master__1__w,
    output logic [7:0] master__1__r,
    output logic [7:0] master__2__w,
    output logic [7:0] master__2__r,
    output logic [7:0] master__3__w,
    output logic [7:0] master__3__r,
    input logic i__0,
    output logic o__0,
    input logic i__1,
    output logic o__1,
    input logic i__2,
    output logic o__2,
    input logic i__3,
    output logic o__3,
    input logic i__4,
    output logic o__4,
    input logic i0,
    input logic i1,
    input logic i2,
    output logic o0,
    output logic o1,
    output logic o2
);


    logic a;  //  default is single bit
    logic b;  //  same as the above
    logic [7:0] c;  //  multi bit bus
    logic [7:0] d;  //  parametric width
    logic [7:0] e;  //  forces signal to be bus and not scalar even if 1 bit wide(range [0:0])
    assign ccc  = {a, b, c};
    assign ccc2 = {8{b}};
    logic [7:0] f__0;  //  port in loop with explicit name
    logic [7:0] f__1;  //  port in loop with explicit name
    logic [7:0] f__2;  //  port in loop with explicit name
    logic [7:0] f__3;  //  port in loop with explicit name
    logic [15:0] g;  //  conditional port
    logic [15:0] h;  //  conditional port
    logic [15:0] i;  //  conditional port
    logic clk;
    logic rst_n;
    logic clk2;
    logic clk2_rstn;
    assign clk   = ext_clk;
    assign rst_n = 1'd1;
    logic [BITS-1:0] z;  //  Verilog parametric port
    assign z = '0;  //  Verilog parametric port

    localparam logic [1:0] IDLE = 2'd0;
    logic [1:0] iii;
    assign iii = IDLE;


    assign b = 1'd1;
    assign e = 8'd3;
    assign f__0 = (d | e);
    assign f__1 = (d | e);
    assign f__2 = (d | e);
    assign f__3 = (d | e);
    assign a = b;
    assign c = 8'd0;
    assign d = (e + 8'd1);
    assign g = {f__1, f__0};
    assign h[7:0] = f__2;
    assign h[15:8] = f__3;
    assign i[0] = h[0];
    assign i[1] = h[1];
    assign i[2] = h[2];
    assign i[3] = h[3];
    assign i[4] = h[4];
    assign i[5] = h[5];
    assign i[6] = h[6];
    assign i[7] = h[7];
    assign i[8] = h[8];
    assign i[9] = h[9];
    assign i[10] = h[10];
    assign i[11] = h[11];
    assign i[12] = h[12];
    assign i[13] = h[13];
    assign i[14] = h[14];
    assign i[15] = h[15];
    logic [7:0] q;
    assign q = 8'd7;

    assign qq = q[7:3];

    assign clk2_rstn = 1'd1;

    assign clk2 = clk;
    logic [7:0] aa;  //  inline assignment
    assign aa = {8{1'b1}};  //  inline assignment

    logic [7:0] bb;  //  inline initial assignment
    initial bb = {8{1'b1}};  //  inline initial assignment


    //  data struct as Python dictionary
    logic [ 7:0] s__ctrl;
    logic [31:0] s__data;
    //  data struct as Python dictionary
    logic [ 7:0] t__ctrl;
    logic [31:0] t__data;

    assign t__ctrl = s__ctrl;
    assign t__data = s__data;

    //  data struct as Python dictionary
    logic [ 7:0] s1__ctrl;
    logic [31:0] s1__data;
    //  data struct as Python dictionary
    logic [ 7:0] t1__ctrl;
    logic [31:0] t1__data;
    assign t1__ctrl = d;

    assign t1__data = s1__data;


    //  data struct as Python dictionary
    logic [7:0] s2__ctrl;
    logic [31:0] s2__data;
    logic s2__valid;
    logic s2__ready;
    //  data struct as Python dictionary
    logic [7:0] t2__ctrl;
    logic [31:0] t2__data;
    logic t2__valid;
    logic t2__ready;

    assign t2__ctrl  = s2__ctrl;
    assign t2__data  = s2__data;
    assign t2__valid = s2__valid;
    assign s2__ready = t2__ready;

    logic [7:0] master_pre__0__w;
    assign master_pre__0__w = {2'd0, c[7:2]};
    assign master__0__w = (master_pre__0__w + 8'd1);
    logic [7:0] master_pre__0__r;
    assign master_pre__0__r = {2'd0, c[7:2]};
    assign master__0__r = (master_pre__0__r + 8'd1);
    logic [7:0] master_pre__1__w;
    assign master_pre__1__w = {2'd0, c[7:2]};
    assign master__1__w = (master_pre__1__w + 8'd1);
    logic [7:0] master_pre__1__r;
    assign master_pre__1__r = {2'd0, c[7:2]};
    assign master__1__r = (master_pre__1__r + 8'd1);
    logic [7:0] master_pre__2__w;
    assign master_pre__2__w = {2'd0, c[7:2]};
    assign master__2__w = (master_pre__2__w + 8'd1);
    logic [7:0] master_pre__2__r;
    assign master_pre__2__r = {2'd0, c[7:2]};
    assign master__2__r = (master_pre__2__r + 8'd1);
    logic [7:0] master_pre__3__w;
    assign master_pre__3__w = {2'd0, c[7:2]};
    assign master__3__w = (master_pre__3__w + 8'd1);
    logic [7:0] master_pre__3__r;
    assign master_pre__3__r = {2'd0, c[7:2]};
    assign master__3__r = (master_pre__3__r + 8'd1);
    assign {o__0, o__1, o__2, o__3, o__4} = {i__0, i__1, i__2, i__3, i__4};
    assign {o0, o1, o2} = {i0, i1, i2};

endmodule  // signals
