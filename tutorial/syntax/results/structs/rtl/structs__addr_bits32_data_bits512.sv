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
    input logic [3:0] master2__awid,
    input logic [31:0] master2__awaddr,
    input logic [1:0] master2__awburst,
    input logic [7:0] master2__awlen,
    input logic [2:0] master2__awsize,
    input logic master2__awvalid,
    output logic master2__awready,
    output logic [3:0] slave2__awid,
    output logic [31:0] slave2__awaddr,
    output logic [1:0] slave2__awburst,
    output logic [7:0] slave2__awlen,
    output logic [2:0] slave2__awsize,
    output logic slave2__awvalid,
    input logic slave2__awready,
    input logic [511:0] master2__wdata,
    input logic [63:0] master2__wstrb,
    input logic master2__wlast,
    input logic master2__wvalid,
    output logic master2__wready,
    output logic [511:0] slave2__wdata,
    output logic [63:0] slave2__wstrb,
    output logic slave2__wlast,
    output logic slave2__wvalid,
    input logic slave2__wready,
    output logic [3:0] master2__bid,
    output logic [1:0] master2__bresp,
    input logic master2__bready,
    output logic master2__bvalid,
    input logic [3:0] slave2__bid,
    input logic [1:0] slave2__bresp,
    output logic slave2__bready,
    input logic slave2__bvalid,
    input logic [3:0] master2__arid,
    input logic [31:0] master2__araddr,
    input logic [1:0] master2__arburst,
    input logic [7:0] master2__arlen,
    input logic [2:0] master2__arsize,
    input logic master2__arvalid,
    output logic master2__arready,
    output logic [3:0] slave2__arid,
    output logic [31:0] slave2__araddr,
    output logic [1:0] slave2__arburst,
    output logic [7:0] slave2__arlen,
    output logic [2:0] slave2__arsize,
    output logic slave2__arvalid,
    input logic slave2__arready,
    output logic [511:0] master2__rdata,
    output logic [3:0] master2__rid,
    output logic [1:0] master2__rresp,
    output logic master2__rlast,
    input logic master2__rready,
    output logic master2__rvalid,
    input logic [511:0] slave2__rdata,
    input logic [3:0] slave2__rid,
    input logic [1:0] slave2__rresp,
    input logic slave2__rlast,
    output logic slave2__rready,
    input logic slave2__rvalid,
    input logic [3:0] master3__awid,
    input logic [31:0] master3__awaddr,
    input logic [1:0] master3__awburst,
    input logic [7:0] master3__awlen,
    input logic [2:0] master3__awsize,
    input logic master3__awvalid,
    output logic master3__awready,
    output logic [3:0] slave3__awid,
    output logic [31:0] slave3__awaddr,
    output logic [1:0] slave3__awburst,
    output logic [7:0] slave3__awlen,
    output logic [2:0] slave3__awsize,
    output logic slave3__awvalid,
    input logic slave3__awready,
    input logic [3:0] master3__arid,
    input logic [31:0] master3__araddr,
    input logic [1:0] master3__arburst,
    input logic [7:0] master3__arlen,
    input logic [2:0] master3__arsize,
    input logic master3__arvalid,
    output logic master3__arready,
    output logic [3:0] slave3__arid,
    output logic [31:0] slave3__araddr,
    output logic [1:0] slave3__arburst,
    output logic [7:0] slave3__arlen,
    output logic [2:0] slave3__arsize,
    output logic slave3__arvalid,
    input logic slave3__arready,
    input logic [511:0] master3__wdata,
    input logic [63:0] master3__wstrb,
    input logic master3__wlast,
    input logic master3__wvalid,
    output logic master3__wready,
    output logic [511:0] slave3__wdata,
    output logic [63:0] slave3__wstrb,
    output logic slave3__wlast,
    output logic slave3__wvalid,
    input logic slave3__wready,
    output logic [3:0] master3__bid,
    output logic [1:0] master3__bresp,
    input logic master3__bready,
    output logic master3__bvalid,
    input logic [3:0] slave3__bid,
    input logic [1:0] slave3__bresp,
    output logic slave3__bready,
    input logic slave3__bvalid,
    output logic [511:0] master3__rdata,
    output logic [3:0] master3__rid,
    output logic [1:0] master3__rresp,
    output logic master3__rlast,
    input logic master3__rready,
    output logic master3__rvalid,
    input logic [511:0] slave3__rdata,
    input logic [3:0] slave3__rid,
    input logic [1:0] slave3__rresp,
    input logic slave3__rlast,
    output logic slave3__rready,
    input logic slave3__rvalid,
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


    assign slave2__awid = master2__awid;
    assign slave2__awaddr = master2__awaddr;
    assign slave2__awburst = master2__awburst;
    assign slave2__awlen = master2__awlen;
    assign slave2__awsize = master2__awsize;
    assign slave2__awvalid = master2__awvalid;
    assign master2__awready = slave2__awready;


    assign slave2__wdata = master2__wdata;
    assign slave2__wstrb = master2__wstrb;
    assign slave2__wlast = master2__wlast;
    assign slave2__wvalid = master2__wvalid;
    assign master2__wready = slave2__wready;


    assign master2__bid = slave2__bid;
    assign master2__bresp = slave2__bresp;
    assign slave2__bready = master2__bready;
    assign master2__bvalid = slave2__bvalid;


    assign slave2__arid = master2__arid;
    assign slave2__araddr = master2__araddr;
    assign slave2__arburst = master2__arburst;
    assign slave2__arlen = master2__arlen;
    assign slave2__arsize = master2__arsize;
    assign slave2__arvalid = master2__arvalid;
    assign master2__arready = slave2__arready;


    assign master2__rdata = slave2__rdata;
    assign master2__rid = slave2__rid;
    assign master2__rresp = slave2__rresp;
    assign master2__rlast = slave2__rlast;
    assign slave2__rready = master2__rready;
    assign master2__rvalid = slave2__rvalid;


    assign master3__awready = slave3__awready;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__awvalid <= 1'd0;
        else if (~(slave3__awvalid) | ~(master3__awready)) slave3__awvalid <= master3__awvalid;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__awid <= 4'd0;
        else if (master3__awvalid & master3__awready) slave3__awid <= master3__awid;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__awaddr <= 32'd0;
        else if (master3__awvalid & master3__awready) slave3__awaddr <= master3__awaddr;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__awburst <= 2'd0;
        else if (master3__awvalid & master3__awready) slave3__awburst <= master3__awburst;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__awlen <= 8'd0;
        else if (master3__awvalid & master3__awready) slave3__awlen <= master3__awlen;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__awsize <= 3'd0;
        else if (master3__awvalid & master3__awready) slave3__awsize <= master3__awsize;



    assign master3__arready = slave3__arready;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__arvalid <= 1'd0;
        else if (~(slave3__arvalid) | ~(master3__arready)) slave3__arvalid <= master3__arvalid;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__arid <= 4'd0;
        else if (master3__arvalid & master3__arready) slave3__arid <= master3__arid;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__araddr <= 32'd0;
        else if (master3__arvalid & master3__arready) slave3__araddr <= master3__araddr;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__arburst <= 2'd0;
        else if (master3__arvalid & master3__arready) slave3__arburst <= master3__arburst;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__arlen <= 8'd0;
        else if (master3__arvalid & master3__arready) slave3__arlen <= master3__arlen;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__arsize <= 3'd0;
        else if (master3__arvalid & master3__arready) slave3__arsize <= master3__arsize;



    assign master3__wready = slave3__wready;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__wvalid <= 1'd0;
        else if (~(slave3__wvalid) | ~(master3__wready)) slave3__wvalid <= master3__wvalid;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__wdata <= 512'd0;
        else if (master3__wvalid & master3__wready) slave3__wdata <= master3__wdata;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__wstrb <= 64'd0;
        else if (master3__wvalid & master3__wready) slave3__wstrb <= master3__wstrb;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__wlast <= 1'd0;
        else if (master3__wvalid & master3__wready) slave3__wlast <= master3__wlast;



    assign master3__bvalid = slave3__bvalid;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__bready <= 1'd0;
        else if (~(slave3__bvalid) | ~(master3__bready)) slave3__bready <= master3__bready;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3__bid <= 4'd0;
        else if (master3__bvalid & master3__bready) master3__bid <= slave3__bid;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3__bresp <= 2'd0;
        else if (master3__bvalid & master3__bready) master3__bresp <= slave3__bresp;



    assign master3__rvalid = slave3__rvalid;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) slave3__rready <= 1'd0;
        else if (~(slave3__rvalid) | ~(master3__rready)) slave3__rready <= master3__rready;



    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3__rdata <= 512'd0;
        else if (master3__rvalid & master3__rready) master3__rdata <= slave3__rdata;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3__rid <= 4'd0;
        else if (master3__rvalid & master3__rready) master3__rid <= slave3__rid;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3__rresp <= 2'd0;
        else if (master3__rvalid & master3__rready) master3__rresp <= slave3__rresp;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) master3__rlast <= 1'd0;
        else if (master3__rvalid & master3__rready) master3__rlast <= slave3__rlast;



    assign bo__a = bi__a;
    assign bo__b = bi__b;


    assign bco__a = bci__a;
    assign bco__b = bci__b;
    assign bco__c = bci__c;


    assign cast_o__a = bi__a;
    assign cast_o__b = bi__b;

    assign cast_o__c = 2'd2;

endmodule  // structs__addr_bits32_data_bits512
