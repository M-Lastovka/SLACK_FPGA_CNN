`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     tb_top_power
// Project Name:    Efficient FPGA CNN implementation
// Description:     Testbench top for power estimation
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

`include "tb_macro_def.svh"

import arith_pckg::*;
import proc_pipe_pckg::*;
import axi_if_pckg::*;
import tb_pckg::*;
import regmap_pckg::*;
import regmap_reg_pckg::*;

module tb_top_power;

logic        clk = 0;
logic        rst_n = 0;

int mm_new_offset;
int mm_offset = 0;

//AXI stream slave interface
logic [C_S_TDATA_WDT-1:0] S_AXIS_TDATA = 0;
logic [C_S_TKEEP_WDT-1:0] S_AXIS_TKEEP = 0;
logic S_AXIS_TLAST = 0;
logic S_AXIS_TVALID = 0;	
logic S_AXIS_TREADY;
//AXI stream master interface
logic [C_M_TDATA_WDT-1:0]  M_AXIS_TDATA;
logic [C_M_TKEEP_WDT-1:0]  M_AXIS_TKEEP;
logic M_AXIS_TLAST;
logic M_AXIS_TVALID;	
logic M_AXIS_TREADY = 0;
//AXI-Lite interface
//write address signals
logic [C_S_AXI_ADDR_WDT-1:0] S_AXI_AWADDR = 0; 
logic [2:0] S_AXI_AWPROT = 0; 
logic S_AXI_AWVALID = 0;
logic S_AXI_AWREADY;
//write data signals
logic [C_S_AXI_DATA_WDT-1:0] S_AXI_WDATA = 0;
logic [C_S_AXI_STRB_WDT-1:0] S_AXI_WSTRB = 0;
logic S_AXI_WVALID = 0; 
logic S_AXI_WREADY;
//write response signals
logic [1:0] S_AXI_BRESP; 
logic S_AXI_BVALID;
logic S_AXI_BREADY = 0;
//read address signals
logic [C_S_AXI_ADDR_WDT-1:0] S_AXI_ARADDR = 0;
logic [2:0] S_AXI_ARPROT = 0; 
logic S_AXI_ARVALID = 0;
logic S_AXI_ARREADY;
//read data signals
logic [C_S_AXI_DATA_WDT-1:0] S_AXI_RDATA;
logic [1:0] S_AXI_RRESP; 
logic S_AXI_RVALID;
logic S_AXI_RREADY = 0;

// Clock generation
initial begin
  forever begin
    #1.25ns 
    clk = ~clk;  
  end
end

initial begin
  $timeformat(-9, 4, " ns", 14);
end

// Reset generation
initial begin
  rst_n = 0;
  #5ns rst_n = 1;
end

initial begin
    #10ns;
    axi_nat_bin_file(C_TEST_MM_PATH, mm_offset, 0, 0, mm_new_offset);
end

initial begin
    #10ns;
    
    forever begin
        @(posedge clk);
    end
end

//write the memory transactions specified in a binary file (specified by offset and length, by default we keep reading
task automatic axi_nat_wr_single
(
    logic [C_S_AXI_DATA_WDT-1:0] axil_wr_data,
    logic [C_S_AXI_ADDR_WDT-1:0] axil_wr_addr
);

`display_verb("TB_TOP_POWER", $sformatf("Start AXI write @start addr: 0x%0h, data: 0x%0h", axil_wr_addr, axil_wr_data), VERB_HIGH)

@(posedge clk); //synchronize to clock edge

fork
    begin
        S_AXI_AWADDR  = axil_wr_addr;
        S_AXI_AWVALID = 1'b1;
        forever begin
            @(posedge clk);
            if(S_AXI_AWVALID & S_AXI_AWREADY) begin
                #1ps;
                S_AXI_AWADDR  = '0;
                S_AXI_AWVALID = '0;
                break;
            end
        end
    end

    begin
        S_AXI_WSTRB   = '1;
        S_AXI_WDATA   = axil_wr_data;
        S_AXI_WVALID  = 1'b1;
        forever begin
            @(posedge clk);
            if(S_AXI_WVALID & S_AXI_WREADY) begin
                #1ps;
                S_AXI_WSTRB   = '0;
                S_AXI_WDATA   = '0;
                S_AXI_WVALID  = 1'b0;
                break;
            end
        end
    end

    begin
        S_AXI_BREADY  = 1'b1; //always accept responses without any delay
        forever begin
            @(posedge clk);
            if(S_AXI_BREADY & S_AXI_BVALID) begin
                #1ps;
                S_AXI_BREADY  = 1'b0;
                break; 
            end
        end
    end
join

`display_verb("TB_TOP_POWER", $sformatf("Done AXI write @start addr: 0x%0h, data: 0x%0h", axil_wr_addr, axil_wr_data), VERB_HIGH)

endtask

//write the memory transactions specified in a binary file (specified by offset and length, by default we keep reading
task automatic axi_nat_bin_file
(
    string file_name,
    int file_trans_offset = 0,
    int file_trans_cnt = 0,
    bit file_ignore = 0,
    output int file_trans_end_offset
);

    int fd = 0;
    logic [C_MM_TRANS_WDT-1:0] temp_trans;
    logic [7:0] mm_dir_buffer;
    logic [C_S_AXI_ADDR_WDT-1:0] mm_addr_buffer;
    logic [C_S_AXI_DATA_WDT-1:0] mm_data_buffer;
    logic [C_S_AXI_STRB_WDT-1:0] mm_str_buffer;
    int scan_r = 0;
    int fseek_ret_val;
    int read_mm_trans_cnt = 0;
    bit read_until_eof = file_trans_cnt == 0; //by default we read until end of file
    `display_verb("TB_TOP_POWER", $sformatf("Generating AXI write transactions by reading a file: %s", file_name), VERB_LOW)
    fd = $fopen(file_name, "rb");
    assert(fd) else $fatal (0, "File could not be opened, exiting simulation!");

    //first skip the transactions before the offset
    fseek_ret_val = $fseek(fd, file_trans_offset*C_MM_TRANS_WDT/8, 0);
    while((read_until_eof & !$feof(fd)) | (!read_until_eof & read_mm_trans_cnt < file_trans_cnt)) begin
        scan_r = $fread(mm_dir_buffer, fd, , 1); 
        scan_r = $fread(mm_addr_buffer, fd, , C_S_AXI_ADDR_WDT/8); 
        scan_r = $fread(mm_data_buffer, fd, , C_S_AXI_DATA_WDT/8);
        scan_r = $fread(mm_str_buffer,  fd, , 1);
        if(scan_r != 0)
            read_mm_trans_cnt++;
        //check for EOB symbol
        if({mm_dir_buffer, mm_addr_buffer, mm_data_buffer, mm_str_buffer} == '0)
            break;
        //switch byte order
        if(C_MM_REV_ENDIAN) begin
            mm_addr_buffer = {<<8{mm_addr_buffer}};
            mm_data_buffer = {<<8{mm_data_buffer}}; 
            mm_str_buffer  = {<<8{mm_str_buffer}};
        end    
        //put transaction on the line
        if(!file_ignore) begin
            if(mm_dir_buffer) begin
                `display_verb("TB_TOP_POWER", $sformatf("New write AXI-lite transaction: (addr: 0x%h data: 0x%h strobe: 0x%h)", mm_addr_buffer, mm_data_buffer, mm_str_buffer), VERB_HIGH)
                axi_nat_wr_single(mm_data_buffer, mm_addr_buffer);
            end
        end
    end
    file_trans_end_offset = read_mm_trans_cnt + file_trans_offset;
    `display_verb("TB_TOP_POWER", $sformatf("Done writing AXI transactions by reading a file: %s", file_name), VERB_LOW)
    $fclose(fd);

endtask

dig_top_wrapp dig_top_inst
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