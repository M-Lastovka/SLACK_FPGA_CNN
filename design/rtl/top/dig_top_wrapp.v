`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     dig_top_wrapp
// Project Name:    Efficient FPGA CNN implementation
// Description:     design verilog wrapper
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////


module dig_top_wrapp
(
    //clk & reset & enable
    input  wire clk,
    input  wire rst_n,
    //AXI stream slave interface
    input  wire [32-1:0] S_AXIS_TDATA,
    input  wire [4-1:0] S_AXIS_TKEEP,
    input  wire S_AXIS_TLAST,
    input  wire S_AXIS_TVALID,	
    output wire S_AXIS_TREADY,
    //AXI stream master interface
    output  wire [32-1:0]  M_AXIS_TDATA,
    output  wire [4-1:0]  M_AXIS_TKEEP,
    output  wire M_AXIS_TLAST,
    output  wire M_AXIS_TVALID,	
    input   wire M_AXIS_TREADY,
    //AXI-Lite interface
    //write address signals
    input  wire [32-1:0] S_AXI_AWADDR, 
    input  wire [2:0] S_AXI_AWPROT, 
    input  wire S_AXI_AWVALID,
    output wire S_AXI_AWREADY,
    //write data signals
    input  wire [32-1:0] S_AXI_WDATA,
    input  wire [4-1:0] S_AXI_WSTRB,
    input  wire S_AXI_WVALID, 
    output wire S_AXI_WREADY,
    //write response signals
    output wire [1:0] S_AXI_BRESP, 
    output wire S_AXI_BVALID,
    input  wire S_AXI_BREADY,
    //read address signals
    input  wire [32-1:0] S_AXI_ARADDR,
    input  wire [2:0] S_AXI_ARPROT, 
    input  wire S_AXI_ARVALID,
    output wire S_AXI_ARREADY,
    //read data signals
    output wire [32-1:0] S_AXI_RDATA,
    output wire [1:0] S_AXI_RRESP, 
    output wire  S_AXI_RVALID,
    input  wire S_AXI_RREADY
);

dig_top dig_top_inst
(
    .clk           (clk          ),
    .rst_n         (rst_n        ),
    .S_AXIS_TDATA  (S_AXIS_TDATA ),
    .S_AXIS_TKEEP  (S_AXIS_TKEEP ),
    .S_AXIS_TLAST  (S_AXIS_TLAST ),
    .S_AXIS_TVALID (S_AXIS_TVALID),	
    .S_AXIS_TREADY (S_AXIS_TREADY),
    .M_AXIS_TDATA  (M_AXIS_TDATA ),
    .M_AXIS_TKEEP  (M_AXIS_TKEEP ),
    .M_AXIS_TLAST  (M_AXIS_TLAST ),
    .M_AXIS_TVALID (M_AXIS_TVALID),	
    .M_AXIS_TREADY (M_AXIS_TREADY),
    .S_AXI_AWADDR  (S_AXI_AWADDR ), 
    .S_AXI_AWPROT  (S_AXI_AWPROT ), 
    .S_AXI_AWVALID (S_AXI_AWVALID),
    .S_AXI_AWREADY (S_AXI_AWREADY),
    .S_AXI_WDATA   (S_AXI_WDATA  ),
    .S_AXI_WSTRB   (S_AXI_WSTRB  ),
    .S_AXI_WVALID  (S_AXI_WVALID ), 
    .S_AXI_WREADY  (S_AXI_WREADY ),
    .S_AXI_BRESP   (S_AXI_BRESP  ), 
    .S_AXI_BVALID  (S_AXI_BVALID ),
    .S_AXI_BREADY  (S_AXI_BREADY ),
    .S_AXI_ARADDR  (S_AXI_ARADDR ),
    .S_AXI_ARPROT  (S_AXI_ARPROT ), 
    .S_AXI_ARVALID (S_AXI_ARVALID),
    .S_AXI_ARREADY (S_AXI_ARREADY),
    .S_AXI_RDATA   (S_AXI_RDATA  ),
    .S_AXI_RRESP   (S_AXI_RRESP  ), 
    .S_AXI_RVALID  (S_AXI_RVALID ),
    .S_AXI_RREADY  (S_AXI_RREADY )
);


endmodule