module signals #(
    parameter int BITS = 32
) (
    input logic ext_clk
);

    // signals module parameters:

    logic a;  //  default is single bit
    logic b;  //  same as the above
    logic [7:0] c;  //  multi bit bus
    logic [7:0] d;  //  parametric width
    logic [7:0] e;  //  forces signal to be bus and not scalar even if 1 bit wide(range [0:0])
    logic [7:0] f0;  //  port in loop with explicit name
    logic [7:0] f1;  //  port in loop with explicit name
    logic [7:0] f2;  //  port in loop with explicit name
    logic [7:0] f3;  //  port in loop with explicit name
    logic [15:0] g;  //  conditional port
    logic [15:0] h;  //  conditional port
    logic clk;
    logic rst_n;
    logic clk2;
    logic clk2_rstn;
    assign clk   = ext_clk;  //  clock assignment
    assign rst_n = 1'd1;  //  reset assignment
    logic [BITS-1:0] z;  //  Verilog parametric port
    assign z = '0;  //  Verilog parametric port

    localparam logic [1:0] IDLE = 2'd0;
    logic [1:0] iii;
    assign iii = IDLE;


    assign b = 1'd1;  //  assign to const
    assign e = 8'd3;  //  assign to const
    assign f0 = (d | e);  //  assign expression
    assign f1 = (d | e);  //  assign expression
    assign f2 = (d | e);  //  assign expression
    assign f3 = (d | e);  //  assign expression
    assign a = b;  //  trivial Verilog assign
    assign c = 8'd0;  //  assign to const
    assign d = (e + 8'd1);  //  assign expression
    assign g = {f0, f1};  //  assign conctenation
    assign h[7:0] = f2;  //  partial bits
    assign h[15:8] = f3;  //  partial bits

    assign clk2_rstn = 1'd1;

    assign clk2 = clk;
    logic [7:0] aa;  //  inline assignment
    assign aa = 8'hff;  //  inline assignment

    logic [7:0] bb;  //  inline initial assignment
    initial bb = 8'hff;  //  inline initial assignment


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
    assign t1__ctrl = d;  //  struct assignment

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


endmodule  // signals
