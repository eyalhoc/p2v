module structs__addr_bits32_data_bits512 (
    input logic clk,
    input logic rst_n,
    input logic [3:0] master0__awid,
    input logic [31:0] master0__awaddr,
    input logic [1:0] master0__awburst,
    input logic [7:0] master0__awlen,
    input logic [2:0] master0__awsize,
    input logic master0__awvalid,
    output logic master0__awready,
    input logic [3:0] master0__arid,
    input logic [31:0] master0__araddr,
    input logic [1:0] master0__arburst,
    input logic [7:0] master0__arlen,
    input logic [2:0] master0__arsize,
    input logic master0__arvalid,
    output logic master0__arready,
    input logic [511:0] master0__wdata,
    input logic [63:0] master0__wstrb,
    input logic master0__wlast,
    input logic master0__wvalid,
    output logic master0__wready,
    output logic [3:0] master0__bid,
    output logic [1:0] master0__bresp,
    input logic master0__bready,
    output logic master0__bvalid,
    output logic [511:0] master0__rdata,
    output logic [3:0] master0__rid,
    output logic [1:0] master0__rresp,
    output logic master0__rlast,
    input logic master0__rready,
    output logic master0__rvalid,
    output logic [3:0] slave0__awid,
    output logic [31:0] slave0__awaddr,
    output logic [1:0] slave0__awburst,
    output logic [7:0] slave0__awlen,
    output logic [2:0] slave0__awsize,
    output logic slave0__awvalid,
    input logic slave0__awready,
    output logic [3:0] slave0__arid,
    output logic [31:0] slave0__araddr,
    output logic [1:0] slave0__arburst,
    output logic [7:0] slave0__arlen,
    output logic [2:0] slave0__arsize,
    output logic slave0__arvalid,
    input logic slave0__arready,
    output logic [511:0] slave0__wdata,
    output logic [63:0] slave0__wstrb,
    output logic slave0__wlast,
    output logic slave0__wvalid,
    input logic slave0__wready,
    input logic [3:0] slave0__bid,
    input logic [1:0] slave0__bresp,
    output logic slave0__bready,
    input logic slave0__bvalid,
    input logic [511:0] slave0__rdata,
    input logic [3:0] slave0__rid,
    input logic [1:0] slave0__rresp,
    input logic slave0__rlast,
    output logic slave0__rready,
    input logic slave0__rvalid,
    input logic [31:0] write_addr,
    input logic [3:0] master1__awid,
    input logic [31:0] master1__awaddr,
    input logic [1:0] master1__awburst,
    input logic [7:0] master1__awlen,
    input logic [2:0] master1__awsize,
    input logic master1__awvalid,
    output logic master1__awready,
    input logic [3:0] master1__arid,
    input logic [31:0] master1__araddr,
    input logic [1:0] master1__arburst,
    input logic [7:0] master1__arlen,
    input logic [2:0] master1__arsize,
    input logic master1__arvalid,
    output logic master1__arready,
    input logic [511:0] master1__wdata,
    input logic [63:0] master1__wstrb,
    input logic master1__wlast,
    input logic master1__wvalid,
    output logic master1__wready,
    output logic [3:0] master1__bid,
    output logic [1:0] master1__bresp,
    input logic master1__bready,
    output logic master1__bvalid,
    output logic [511:0] master1__rdata,
    output logic [3:0] master1__rid,
    output logic [1:0] master1__rresp,
    output logic master1__rlast,
    input logic master1__rready,
    output logic master1__rvalid,
    output logic [3:0] slave1__awid,
    output logic [31:0] slave1__awaddr,
    output logic [1:0] slave1__awburst,
    output logic [7:0] slave1__awlen,
    output logic [2:0] slave1__awsize,
    output logic slave1__awvalid,
    input logic slave1__awready,
    output logic [3:0] slave1__arid,
    output logic [31:0] slave1__araddr,
    output logic [1:0] slave1__arburst,
    output logic [7:0] slave1__arlen,
    output logic [2:0] slave1__arsize,
    output logic slave1__arvalid,
    input logic slave1__arready,
    output logic [511:0] slave1__wdata,
    output logic [63:0] slave1__wstrb,
    output logic slave1__wlast,
    output logic slave1__wvalid,
    input logic slave1__wready,
    input logic [3:0] slave1__bid,
    input logic [1:0] slave1__bresp,
    output logic slave1__bready,
    input logic slave1__bvalid,
    input logic [511:0] slave1__rdata,
    input logic [3:0] slave1__rid,
    input logic [1:0] slave1__rresp,
    input logic slave1__rlast,
    output logic slave1__rready,
    input logic slave1__rvalid,
    input logic [3:0] master2_aw__id,
    input logic [31:0] master2_aw__addr,
    input logic [1:0] master2_aw__burst,
    input logic [7:0] master2_aw__len,
    input logic [2:0] master2_aw__size,
    input logic master2_aw__valid,
    output logic master2_aw__ready,
    output logic [3:0] slave2_aw__id,
    output logic [31:0] slave2_aw__addr,
    output logic [1:0] slave2_aw__burst,
    output logic [7:0] slave2_aw__len,
    output logic [2:0] slave2_aw__size,
    output logic slave2_aw__valid,
    input logic slave2_aw__ready,
    input logic [511:0] master2_w__data,
    input logic [63:0] master2_w__strb,
    input logic master2_w__last,
    input logic master2_w__valid,
    output logic master2_w__ready,
    output logic [511:0] slave2_w__data,
    output logic [63:0] slave2_w__strb,
    output logic slave2_w__last,
    output logic slave2_w__valid,
    input logic slave2_w__ready,
    output logic [3:0] master2_b__id,
    output logic [1:0] master2_b__resp,
    input logic master2_b__ready,
    output logic master2_b__valid,
    input logic [3:0] slave2_b__id,
    input logic [1:0] slave2_b__resp,
    output logic slave2_b__ready,
    input logic slave2_b__valid,
    input logic [3:0] master2_ar__id,
    input logic [31:0] master2_ar__addr,
    input logic [1:0] master2_ar__burst,
    input logic [7:0] master2_ar__len,
    input logic [2:0] master2_ar__size,
    input logic master2_ar__valid,
    output logic master2_ar__ready,
    output logic [3:0] slave2_ar__id,
    output logic [31:0] slave2_ar__addr,
    output logic [1:0] slave2_ar__burst,
    output logic [7:0] slave2_ar__len,
    output logic [2:0] slave2_ar__size,
    output logic slave2_ar__valid,
    input logic slave2_ar__ready,
    output logic [511:0] master2_r__data,
    output logic [3:0] master2_r__id,
    output logic [1:0] master2_r__resp,
    output logic master2_r__last,
    input logic master2_r__ready,
    output logic master2_r__valid,
    input logic [511:0] slave2_r__data,
    input logic [3:0] slave2_r__id,
    input logic [1:0] slave2_r__resp,
    input logic slave2_r__last,
    output logic slave2_r__ready,
    input logic slave2_r__valid,
    input logic [3:0] master3_aw__id,
    input logic [31:0] master3_aw__addr,
    input logic [1:0] master3_aw__burst,
    input logic [7:0] master3_aw__len,
    input logic [2:0] master3_aw__size,
    input logic master3_aw__valid,
    output logic master3_aw__ready,
    output logic [3:0] slave3_aw__id,
    output logic [31:0] slave3_aw__addr,
    output logic [1:0] slave3_aw__burst,
    output logic [7:0] slave3_aw__len,
    output logic [2:0] slave3_aw__size,
    output logic slave3_aw__valid,
    input logic slave3_aw__ready,
    input logic [3:0] master3_ar__id,
    input logic [31:0] master3_ar__addr,
    input logic [1:0] master3_ar__burst,
    input logic [7:0] master3_ar__len,
    input logic [2:0] master3_ar__size,
    input logic master3_ar__valid,
    output logic master3_ar__ready,
    output logic [3:0] slave3_ar__id,
    output logic [31:0] slave3_ar__addr,
    output logic [1:0] slave3_ar__burst,
    output logic [7:0] slave3_ar__len,
    output logic [2:0] slave3_ar__size,
    output logic slave3_ar__valid,
    input logic slave3_ar__ready,
    input logic [511:0] master3_w__data,
    input logic [63:0] master3_w__strb,
    input logic master3_w__last,
    input logic master3_w__valid,
    output logic master3_w__ready,
    output logic [511:0] slave3_w__data,
    output logic [63:0] slave3_w__strb,
    output logic slave3_w__last,
    output logic slave3_w__valid,
    input logic slave3_w__ready,
    output logic [3:0] master3_b__id,
    output logic [1:0] master3_b__resp,
    input logic master3_b__ready,
    output logic master3_b__valid,
    input logic [3:0] slave3_b__id,
    input logic [1:0] slave3_b__resp,
    output logic slave3_b__ready,
    input logic slave3_b__valid,
    output logic [511:0] master3_r__data,
    output logic [3:0] master3_r__id,
    output logic [1:0] master3_r__resp,
    output logic master3_r__last,
    input logic master3_r__ready,
    output logic master3_r__valid,
    input logic [511:0] slave3_r__data,
    input logic [3:0] slave3_r__id,
    input logic [1:0] slave3_r__resp,
    input logic slave3_r__last,
    output logic slave3_r__ready,
    input logic slave3_r__valid,
    input logic [7:0] bi__a,
    input logic [3:0] bi__b,
    output logic [7:0] bo__a,
    output logic [3:0] bo__b,
    input logic [7:0] bci__a,
    input logic [3:0] bci__b,
    input logic [1:0] bci__c,
    output logic [7:0] bco__a,
    output logic [3:0] bco__b,
    output logic [1:0] bco__c,
    output logic [7:0] cast_o__a,
    output logic [3:0] cast_o__b,
    output logic [1:0] cast_o__c
);

    // module parameters:
    // clk = p2v_clock.clk_arst() (p2v_clock)
    // addr_bits = 32 (int)
    // data_bits = 512 (int)


    assign slave0__awid = master0__awid;
    assign slave0__awaddr = master0__awaddr;
    assign slave0__awburst = master0__awburst;
    assign slave0__awlen = master0__awlen;
    assign slave0__awsize = master0__awsize;
    assign slave0__awvalid = master0__awvalid;
    assign master0__awready = slave0__awready;
    assign slave0__arid = master0__arid;
    assign slave0__araddr = master0__araddr;
    assign slave0__arburst = master0__arburst;
    assign slave0__arlen = master0__arlen;
    assign slave0__arsize = master0__arsize;
    assign slave0__arvalid = master0__arvalid;
    assign master0__arready = slave0__arready;
    assign slave0__wdata = master0__wdata;
    assign slave0__wstrb = master0__wstrb;
    assign slave0__wlast = master0__wlast;
    assign slave0__wvalid = master0__wvalid;
    assign master0__wready = slave0__wready;
    assign master0__bid = slave0__bid;
    assign master0__bresp = slave0__bresp;
    assign slave0__bready = master0__bready;
    assign master0__bvalid = slave0__bvalid;
    assign master0__rdata = slave0__rdata;
    assign master0__rid = slave0__rid;
    assign master0__rresp = slave0__rresp;
    assign master0__rlast = slave0__rlast;
    assign slave0__rready = master0__rready;
    assign master0__rvalid = slave0__rvalid;

    assign slave1__awaddr = write_addr;

    assign slave1__awid = master1__awid;
    assign slave1__awburst = master1__awburst;
    assign slave1__awlen = master1__awlen;
    assign slave1__awsize = master1__awsize;
    assign slave1__awvalid = master1__awvalid;
    assign master1__awready = slave1__awready;
    assign slave1__arid = master1__arid;
    assign slave1__araddr = master1__araddr;
    assign slave1__arburst = master1__arburst;
    assign slave1__arlen = master1__arlen;
    assign slave1__arsize = master1__arsize;
    assign slave1__arvalid = master1__arvalid;
    assign master1__arready = slave1__arready;
    assign slave1__wdata = master1__wdata;
    assign slave1__wstrb = master1__wstrb;
    assign slave1__wlast = master1__wlast;
    assign slave1__wvalid = master1__wvalid;
    assign master1__wready = slave1__wready;
    assign master1__bid = slave1__bid;
    assign master1__bresp = slave1__bresp;
    assign slave1__bready = master1__bready;
    assign master1__bvalid = slave1__bvalid;
    assign master1__rdata = slave1__rdata;
    assign master1__rid = slave1__rid;
    assign master1__rresp = slave1__rresp;
    assign master1__rlast = slave1__rlast;
    assign slave1__rready = master1__rready;
    assign master1__rvalid = slave1__rvalid;


    assign slave2_aw__id = master2_aw__id;
    assign slave2_aw__addr = master2_aw__addr;
    assign slave2_aw__burst = master2_aw__burst;
    assign slave2_aw__len = master2_aw__len;
    assign slave2_aw__size = master2_aw__size;
    assign slave2_aw__valid = master2_aw__valid;
    assign master2_aw__ready = slave2_aw__ready;


    assign slave2_w__data = master2_w__data;
    assign slave2_w__strb = master2_w__strb;
    assign slave2_w__last = master2_w__last;
    assign slave2_w__valid = master2_w__valid;
    assign master2_w__ready = slave2_w__ready;


    assign master2_b__id = slave2_b__id;
    assign master2_b__resp = slave2_b__resp;
    assign slave2_b__ready = master2_b__ready;
    assign master2_b__valid = slave2_b__valid;


    assign slave2_ar__id = master2_ar__id;
    assign slave2_ar__addr = master2_ar__addr;
    assign slave2_ar__burst = master2_ar__burst;
    assign slave2_ar__len = master2_ar__len;
    assign slave2_ar__size = master2_ar__size;
    assign slave2_ar__valid = master2_ar__valid;
    assign master2_ar__ready = slave2_ar__ready;


    assign master2_r__data = slave2_r__data;
    assign master2_r__id = slave2_r__id;
    assign master2_r__resp = slave2_r__resp;
    assign master2_r__last = slave2_r__last;
    assign slave2_r__ready = master2_r__ready;
    assign master2_r__valid = slave2_r__valid;


    assign master3_aw__ready = slave3_aw__ready;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_aw__valid <= 1'd0;
        else if (~slave3_aw__valid | ~master3_aw__ready) slave3_aw__valid <= master3_aw__valid;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_aw__id <= 4'd0;
        else if (master3_aw__valid & master3_aw__ready) slave3_aw__id <= master3_aw__id;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_aw__addr <= 32'd0;
        else if (master3_aw__valid & master3_aw__ready) slave3_aw__addr <= master3_aw__addr;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_aw__burst <= 2'd0;
        else if (master3_aw__valid & master3_aw__ready) slave3_aw__burst <= master3_aw__burst;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_aw__len <= 8'd0;
        else if (master3_aw__valid & master3_aw__ready) slave3_aw__len <= master3_aw__len;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_aw__size <= 3'd0;
        else if (master3_aw__valid & master3_aw__ready) slave3_aw__size <= master3_aw__size;



    assign master3_ar__ready = slave3_ar__ready;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_ar__valid <= 1'd0;
        else if (~slave3_ar__valid | ~master3_ar__ready) slave3_ar__valid <= master3_ar__valid;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_ar__id <= 4'd0;
        else if (master3_ar__valid & master3_ar__ready) slave3_ar__id <= master3_ar__id;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_ar__addr <= 32'd0;
        else if (master3_ar__valid & master3_ar__ready) slave3_ar__addr <= master3_ar__addr;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_ar__burst <= 2'd0;
        else if (master3_ar__valid & master3_ar__ready) slave3_ar__burst <= master3_ar__burst;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_ar__len <= 8'd0;
        else if (master3_ar__valid & master3_ar__ready) slave3_ar__len <= master3_ar__len;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_ar__size <= 3'd0;
        else if (master3_ar__valid & master3_ar__ready) slave3_ar__size <= master3_ar__size;



    assign master3_w__ready = slave3_w__ready;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_w__valid <= 1'd0;
        else if (~slave3_w__valid | ~master3_w__ready) slave3_w__valid <= master3_w__valid;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_w__data <= 512'd0;
        else if (master3_w__valid & master3_w__ready) slave3_w__data <= master3_w__data;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_w__strb <= 64'd0;
        else if (master3_w__valid & master3_w__ready) slave3_w__strb <= master3_w__strb;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_w__last <= 1'd0;
        else if (master3_w__valid & master3_w__ready) slave3_w__last <= master3_w__last;



    assign master3_b__valid = slave3_b__valid;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_b__ready <= 1'd0;
        else if (~slave3_b__ready | ~master3_b__valid) slave3_b__ready <= master3_b__ready;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_b__id <= 4'd0;
        else if (master3_b__ready & master3_b__valid) master3_b__id <= slave3_b__id;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_b__resp <= 2'd0;
        else if (master3_b__ready & master3_b__valid) master3_b__resp <= slave3_b__resp;



    assign master3_r__valid = slave3_r__valid;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_r__ready <= 1'd0;
        else if (~slave3_r__ready | ~master3_r__valid) slave3_r__ready <= master3_r__ready;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_r__data <= 512'd0;
        else if (master3_r__ready & master3_r__valid) master3_r__data <= slave3_r__data;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_r__id <= 4'd0;
        else if (master3_r__ready & master3_r__valid) master3_r__id <= slave3_r__id;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_r__resp <= 2'd0;
        else if (master3_r__ready & master3_r__valid) master3_r__resp <= slave3_r__resp;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_r__last <= 1'd0;
        else if (master3_r__ready & master3_r__valid) master3_r__last <= slave3_r__last;



    assign bo__a = bi__a;
    assign bo__b = bi__b;


    assign bco__a = bci__a;
    assign bco__b = bci__b;
    assign bco__c = bci__c;


    assign cast_o__a = bi__a;
    assign cast_o__b = bi__b;

    assign cast_o__c = 2'd2;

endmodule
