module structs__addr_bits32_data_bits512 (
    input logic clk,
    input logic rst_n,
    input logic [3:0] mstr0__awid,
    input logic [31:0] mstr0__awaddr,
    input logic [1:0] mstr0__awburst,
    input logic [7:0] mstr0__awlen,
    input logic [2:0] mstr0__awsize,
    input logic mstr0__awvalid,
    output logic mstr0__awready,
    input logic [3:0] mstr0__arid,
    input logic [31:0] mstr0__araddr,
    input logic [1:0] mstr0__arburst,
    input logic [7:0] mstr0__arlen,
    input logic [2:0] mstr0__arsize,
    input logic mstr0__arvalid,
    output logic mstr0__arready,
    input logic [511:0] mstr0__wdata,
    input logic [63:0] mstr0__wstrb,
    input logic mstr0__wlast,
    input logic mstr0__wvalid,
    output logic mstr0__wready,
    output logic [3:0] mstr0__bid,
    output logic [1:0] mstr0__bresp,
    input logic mstr0__bready,
    output logic mstr0__bvalid,
    output logic [511:0] mstr0__rdata,
    output logic [3:0] mstr0__rid,
    output logic [1:0] mstr0__rresp,
    output logic mstr0__rlast,
    input logic mstr0__rready,
    output logic mstr0__rvalid,
    output logic [3:0] slv0__awid,
    output logic [31:0] slv0__awaddr,
    output logic [1:0] slv0__awburst,
    output logic [7:0] slv0__awlen,
    output logic [2:0] slv0__awsize,
    output logic slv0__awvalid,
    input logic slv0__awready,
    output logic [3:0] slv0__arid,
    output logic [31:0] slv0__araddr,
    output logic [1:0] slv0__arburst,
    output logic [7:0] slv0__arlen,
    output logic [2:0] slv0__arsize,
    output logic slv0__arvalid,
    input logic slv0__arready,
    output logic [511:0] slv0__wdata,
    output logic [63:0] slv0__wstrb,
    output logic slv0__wlast,
    output logic slv0__wvalid,
    input logic slv0__wready,
    input logic [3:0] slv0__bid,
    input logic [1:0] slv0__bresp,
    output logic slv0__bready,
    input logic slv0__bvalid,
    input logic [511:0] slv0__rdata,
    input logic [3:0] slv0__rid,
    input logic [1:0] slv0__rresp,
    input logic slv0__rlast,
    output logic slv0__rready,
    input logic slv0__rvalid,
    input logic [31:0] write_addr,
    input logic [3:0] mstr1__awid,
    input logic [31:0] mstr1__awaddr,
    input logic [1:0] mstr1__awburst,
    input logic [7:0] mstr1__awlen,
    input logic [2:0] mstr1__awsize,
    input logic mstr1__awvalid,
    output logic mstr1__awready,
    input logic [3:0] mstr1__arid,
    input logic [31:0] mstr1__araddr,
    input logic [1:0] mstr1__arburst,
    input logic [7:0] mstr1__arlen,
    input logic [2:0] mstr1__arsize,
    input logic mstr1__arvalid,
    output logic mstr1__arready,
    input logic [511:0] mstr1__wdata,
    input logic [63:0] mstr1__wstrb,
    input logic mstr1__wlast,
    input logic mstr1__wvalid,
    output logic mstr1__wready,
    output logic [3:0] mstr1__bid,
    output logic [1:0] mstr1__bresp,
    input logic mstr1__bready,
    output logic mstr1__bvalid,
    output logic [511:0] mstr1__rdata,
    output logic [3:0] mstr1__rid,
    output logic [1:0] mstr1__rresp,
    output logic mstr1__rlast,
    input logic mstr1__rready,
    output logic mstr1__rvalid,
    output logic [3:0] slv1__awid,
    output logic [31:0] slv1__awaddr,
    output logic [1:0] slv1__awburst,
    output logic [7:0] slv1__awlen,
    output logic [2:0] slv1__awsize,
    output logic slv1__awvalid,
    input logic slv1__awready,
    output logic [3:0] slv1__arid,
    output logic [31:0] slv1__araddr,
    output logic [1:0] slv1__arburst,
    output logic [7:0] slv1__arlen,
    output logic [2:0] slv1__arsize,
    output logic slv1__arvalid,
    input logic slv1__arready,
    output logic [511:0] slv1__wdata,
    output logic [63:0] slv1__wstrb,
    output logic slv1__wlast,
    output logic slv1__wvalid,
    input logic slv1__wready,
    input logic [3:0] slv1__bid,
    input logic [1:0] slv1__bresp,
    output logic slv1__bready,
    input logic slv1__bvalid,
    input logic [511:0] slv1__rdata,
    input logic [3:0] slv1__rid,
    input logic [1:0] slv1__rresp,
    input logic slv1__rlast,
    output logic slv1__rready,
    input logic slv1__rvalid,
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

    // structs module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * addr_bits = 32 (int) # None
    //  * data_bits = 512 (int) # None


    assign slv0__awid = mstr0__awid;
    assign slv0__awaddr = mstr0__awaddr;
    assign slv0__awburst = mstr0__awburst;
    assign slv0__awlen = mstr0__awlen;
    assign slv0__awsize = mstr0__awsize;
    assign slv0__awvalid = mstr0__awvalid;
    assign mstr0__awready = slv0__awready;
    assign slv0__arid = mstr0__arid;
    assign slv0__araddr = mstr0__araddr;
    assign slv0__arburst = mstr0__arburst;
    assign slv0__arlen = mstr0__arlen;
    assign slv0__arsize = mstr0__arsize;
    assign slv0__arvalid = mstr0__arvalid;
    assign mstr0__arready = slv0__arready;
    assign slv0__wdata = mstr0__wdata;
    assign slv0__wstrb = mstr0__wstrb;
    assign slv0__wlast = mstr0__wlast;
    assign slv0__wvalid = mstr0__wvalid;
    assign mstr0__wready = slv0__wready;
    assign mstr0__bid = slv0__bid;
    assign mstr0__bresp = slv0__bresp;
    assign slv0__bready = mstr0__bready;
    assign mstr0__bvalid = slv0__bvalid;
    assign mstr0__rdata = slv0__rdata;
    assign mstr0__rid = slv0__rid;
    assign mstr0__rresp = slv0__rresp;
    assign mstr0__rlast = slv0__rlast;
    assign slv0__rready = mstr0__rready;
    assign mstr0__rvalid = slv0__rvalid;

    assign slv1__awaddr = write_addr;

    assign slv1__awid = mstr1__awid;
    assign slv1__awburst = mstr1__awburst;
    assign slv1__awlen = mstr1__awlen;
    assign slv1__awsize = mstr1__awsize;
    assign slv1__awvalid = mstr1__awvalid;
    assign mstr1__awready = slv1__awready;
    assign slv1__arid = mstr1__arid;
    assign slv1__araddr = mstr1__araddr;
    assign slv1__arburst = mstr1__arburst;
    assign slv1__arlen = mstr1__arlen;
    assign slv1__arsize = mstr1__arsize;
    assign slv1__arvalid = mstr1__arvalid;
    assign mstr1__arready = slv1__arready;
    assign slv1__wdata = mstr1__wdata;
    assign slv1__wstrb = mstr1__wstrb;
    assign slv1__wlast = mstr1__wlast;
    assign slv1__wvalid = mstr1__wvalid;
    assign mstr1__wready = slv1__wready;
    assign mstr1__bid = slv1__bid;
    assign mstr1__bresp = slv1__bresp;
    assign slv1__bready = mstr1__bready;
    assign mstr1__bvalid = slv1__bvalid;
    assign mstr1__rdata = slv1__rdata;
    assign mstr1__rid = slv1__rid;
    assign mstr1__rresp = slv1__rresp;
    assign mstr1__rlast = slv1__rlast;
    assign slv1__rready = mstr1__rready;
    assign mstr1__rvalid = slv1__rvalid;


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
        else if (~(slave3_aw__valid) | ~(master3_aw__ready)) slave3_aw__valid <= master3_aw__valid;



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
        else if (~(slave3_ar__valid) | ~(master3_ar__ready)) slave3_ar__valid <= master3_ar__valid;



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
        else if (~(slave3_w__valid) | ~(master3_w__ready)) slave3_w__valid <= master3_w__valid;



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
        else if (~(slave3_b__valid) | ~(master3_b__ready)) slave3_b__ready <= master3_b__ready;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_b__id <= 4'd0;
        else if (master3_b__valid & master3_b__ready) master3_b__id <= slave3_b__id;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_b__resp <= 2'd0;
        else if (master3_b__valid & master3_b__ready) master3_b__resp <= slave3_b__resp;



    assign master3_r__valid = slave3_r__valid;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3_r__ready <= 1'd0;
        else if (~(slave3_r__valid) | ~(master3_r__ready)) slave3_r__ready <= master3_r__ready;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_r__data <= 512'd0;
        else if (master3_r__valid & master3_r__ready) master3_r__data <= slave3_r__data;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_r__id <= 4'd0;
        else if (master3_r__valid & master3_r__ready) master3_r__id <= slave3_r__id;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_r__resp <= 2'd0;
        else if (master3_r__valid & master3_r__ready) master3_r__resp <= slave3_r__resp;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3_r__last <= 1'd0;
        else if (master3_r__valid & master3_r__ready) master3_r__last <= slave3_r__last;



    assign bo__a = bi__a;
    assign bo__b = bi__b;


    assign bco__a = bci__a;
    assign bco__b = bci__b;
    assign bco__c = bci__c;


    assign cast_o__a = bi__a;
    assign cast_o__b = bi__b;

    assign cast_o__c = 2'd2;

endmodule  // structs__addr_bits32_data_bits512
