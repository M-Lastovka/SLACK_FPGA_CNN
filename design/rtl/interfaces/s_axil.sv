`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     s_axil
// Project Name:    Efficient FPGA CNN implementation
// Description:     AXI-Lite Slave
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import axi_if_pckg::*;
import regmap_pckg::*;
import regmap_reg_pckg::*;
import proc_pipe_pckg::*;
import perf_cnt_pckg::*;

module s_axil
(
    //clk&reset
    input logic S_AXI_ACLK,
    input logic S_AXI_ARESETN,
    //AXI-Lite interface
    //write address signals
    input  logic [C_S_AXI_ADDR_WDT-1:0] S_AXI_AWADDR, 
    input  logic [2:0] S_AXI_AWPROT, 
    input  logic S_AXI_AWVALID,
    output logic S_AXI_AWREADY,
    //write data signals
    input  logic [C_S_AXI_DATA_WDT-1:0] S_AXI_WDATA,
    input  logic [C_S_AXI_STRB_WDT-1:0] S_AXI_WSTRB,
    input  logic S_AXI_WVALID, 
    output logic S_AXI_WREADY,
    //write response signals
    output logic [1:0] S_AXI_BRESP, 
    output logic S_AXI_BVALID,
    input  logic S_AXI_BREADY,
    //read address signals
    input  logic [C_S_AXI_ADDR_WDT-1:0] S_AXI_ARADDR,
    input  logic [2:0] S_AXI_ARPROT, 
    input  logic S_AXI_ARVALID,
    output logic S_AXI_ARREADY,
    //read data signals
    output logic [C_S_AXI_DATA_WDT-1:0] S_AXI_RDATA,
    output logic [1:0] S_AXI_RRESP, 
    output logic S_AXI_RVALID,
    input  logic S_AXI_RREADY,
    regmap_rd_if.requester s_axil_regmap_rd_if,
    regmap_wr_if.requester s_axil_regmap_wr_if
);

//-------------------------------------------------------------
//Read channel-------------------------------------------------
//-------------------------------------------------------------

logic rd_resp_stall;
logic val_rd_req;
logic rd_addr_accept;
logic skid_buffer_ar_wr_en;
logic skid_buffer_ar_rd_en;
logic [C_S_AXI_ADDR_WDT-1:0] skid_buff_ar;
logic rd_resp_accept;
logic s_axil_en;
logic s_axil_en_i;
logic [C_S_AXI_DATA_WDT-1:0] skid_buff_r;
logic skid_buff_r_val;
logic rvalid_next_cyc;
logic [$clog2(C_S_AXI_REGMAP_CYC_LEN+1):0] rvalid_cnt;
logic wait_for_rd_resp;

assign rd_resp_stall = (S_AXI_RVALID & !S_AXI_RREADY); //master is stalling the read response
assign val_rd_req = (S_AXI_ARVALID | !S_AXI_ARREADY) & s_axil_en_i & !wait_for_rd_resp; //valid read request has been issued 
assign rd_addr_accept = (S_AXI_ARVALID & S_AXI_ARREADY); //read request is accepted this cycle
assign rd_resp_accept = (S_AXI_RVALID & S_AXI_RREADY); //read response is accepted this cycle
assign S_AXI_RRESP = '0; //always return OK status
//araddr skid buffer is not needed now, since arready always waits until read accept
assign skid_buffer_ar_wr_en = 1'b0;
assign skid_buffer_ar_rd_en = 1'b0;
assign rvalid_next_cyc = (rvalid_cnt >= C_S_AXI_REGMAP_CYC_LEN & C_S_AXI_REGMAP_CYC_LEN > 0) | (C_S_AXI_REGMAP_CYC_LEN == 0 & val_rd_req); //read data will be valid after the counter has reached max value

always_ff @(posedge S_AXI_ACLK) begin : read_channel_proc
    if (!S_AXI_ARESETN) begin
        S_AXI_RVALID     <= 1'b0;
        S_AXI_ARREADY    <= 1'b0;
        skid_buff_ar     <= '0;
        skid_buff_r      <= '0;
        skid_buff_r_val  <= 1'b0;
        s_axil_en        <= 1'b0;
        s_axil_en_i      <= 1'b0;
        rvalid_cnt       <= '0;
        wait_for_rd_resp <= 1'b0;
    end else begin
        s_axil_en   <= 1'b1; //always enabled
        s_axil_en_i <= s_axil_en;

        if(s_axil_en) begin //accept read requests only if enabled
            if(!wait_for_rd_resp) begin
                if(!s_axil_en_i) begin
                    S_AXI_ARREADY <= 1'b1; //came out of reset or disable
                end else if(S_AXI_ARREADY & S_AXI_ARVALID) begin //deassert ready until read is accepted
                    S_AXI_ARREADY    <= 1'b0; 
                    wait_for_rd_resp <= 1'b1;
                end else begin
                    S_AXI_ARREADY    <= 1'b1; 
                end
            end else begin
                if(rd_resp_accept) begin //read accepted
                    S_AXI_ARREADY    <= 1'b1; 
                    wait_for_rd_resp <= 1'b0;
                end
            end
        end

        if((val_rd_req & rvalid_cnt == 0) | (rvalid_cnt < C_S_AXI_REGMAP_CYC_LEN & rvalid_cnt != 0)) //increment - either when the valid request is accepted or we started counting and not yet finished
            rvalid_cnt <= rvalid_cnt + 1;
        else if(rvalid_cnt >= C_S_AXI_REGMAP_CYC_LEN) //reset once the valid read data arrives
            rvalid_cnt <= '0;
            
        if(rd_resp_stall | rvalid_next_cyc) //keep rvalid high if response is stalled or the read request data will arrive next cycle
            S_AXI_RVALID <= 1'b1;
        else
            S_AXI_RVALID <= 1'b0;
        if(skid_buffer_ar_wr_en) //buffer the address on a master stall and read request is accepted aswell
            skid_buff_ar <= S_AXI_ARADDR;

        if(rd_resp_stall & !skid_buff_r_val) begin
            skid_buff_r_val <= 1'b1;
            skid_buff_r     <= s_axil_regmap_rd_if.rd_data;
        end else if(!rd_resp_stall & skid_buff_r_val) begin
            skid_buff_r_val <= 1'b0;
            skid_buff_r     <= '0;
        end
    end
end

//-------------------------------------------------------------
//Write channel------------------------------------------------
//-------------------------------------------------------------

logic val_wr_addr;
logic val_wr_data;
logic wr_resp_stall;
logic wr_resp_accept;
logic skid_buffer_aw_wr_en;
logic skid_buffer_aw_rd_en;
logic skid_buffer_w_wr_en;
logic skid_buffer_w_rd_en;
logic [C_S_AXI_ADDR_WDT-1:0] skid_buff_aw;
logic [C_S_AXI_DATA_WDT-1:0] skid_buff_w;
logic [C_S_AXI_STRB_WDT-1:0] skid_buff_wstr;
logic wr_addr_accept;
logic wr_data_accept;

assign val_wr_addr = (S_AXI_AWVALID | !S_AXI_AWREADY) & s_axil_en_i; //we have a valid write address, either in skid buffer or on the line
assign val_wr_data = (S_AXI_WVALID | !S_AXI_WREADY) & s_axil_en_i; //we have a valid write data, either in skid buffer or on the line
assign wr_resp_stall = S_AXI_BVALID & !S_AXI_BREADY; //response channel stalled by master
assign wr_addr_accept = S_AXI_AWVALID & S_AXI_AWREADY; //address is accepted this cycle
assign wr_data_accept = S_AXI_WVALID & S_AXI_WREADY; //data is accepted this cycle
assign wr_resp_accept = S_AXI_BVALID & S_AXI_BREADY; //write response is accepted this cycle
assign S_AXI_BRESP = '0; //always return OK status

//write to the skid buffer if we are accepting address while data is not yet available or the write response is stalled
assign skid_buffer_aw_wr_en = wr_addr_accept & (wr_resp_stall | !val_wr_data);
//use skid buffer address on the moment where write response is unstalled, while write address is still stalled
assign skid_buffer_aw_rd_en = (!wr_resp_stall & !S_AXI_AWREADY) & s_axil_en_i;

//write to the skid buffer if we are accepting data while address is not yet available or the write response is stalled
assign skid_buffer_w_wr_en = wr_data_accept & (wr_resp_stall | !val_wr_addr);

//use skid buffer data on the moment where write response is unstalled, while write data is still stalled
assign skid_buffer_w_rd_en = (!wr_resp_stall & !S_AXI_WREADY) & s_axil_en;

always_ff @(posedge S_AXI_ACLK) begin: write_channel_proc
    if(!S_AXI_ARESETN) begin
        S_AXI_AWREADY   <= 1'b0;
        S_AXI_WREADY    <= 1'b0;
        S_AXI_BVALID    <= 1'b0;
        skid_buff_aw    <= '0;
        skid_buff_w     <= '0;
        skid_buff_wstr  <= '0;
    end else begin
        if(s_axil_en)
            if(!s_axil_en_i)
                S_AXI_AWREADY <= 1'b1;
            else if(wr_resp_stall) //deassert awready if read response is stalled & there is valid address on the line
                S_AXI_AWREADY <= !val_wr_addr;
            else if(val_wr_data) //valid data either on the line or in a buffer, ready to accept address in any case
                S_AXI_AWREADY <= 1'b1;
            else if(wr_resp_stall) //deassert awready if read response is stalled & there is valid address on the line
                S_AXI_AWREADY <= !val_wr_addr;
            else if(val_wr_data) //valid data either on the line or in a buffer, ready to accept address in any case    
                S_AXI_AWREADY <= 1'b1;
            else //write response is not stalled, no valid data, keep ready up until valid address comes up
                S_AXI_AWREADY <= S_AXI_AWREADY & !S_AXI_AWVALID;
        else
            S_AXI_AWREADY <= 1'b0;     
        
        if(s_axil_en)
            if(!s_axil_en_i)
                S_AXI_WREADY <= 1'b1;
            else if (wr_resp_stall) //deassert wready if read response is stalled & there is valid data on the line
                S_AXI_WREADY <= !val_wr_data; 
            else if(val_wr_addr) //valid address either on the line or in a buffer, ready to accept data in any case
                S_AXI_WREADY <= 1'b1;        
            else //write response is not stalled, no valid address, keep ready up until valid data comes up
                S_AXI_WREADY <= S_AXI_WREADY & !S_AXI_WVALID;
        else
            S_AXI_WREADY <= 1'b0;   
        
        if(skid_buffer_aw_wr_en) //buffer the address on a master stall and read request is accepted aswell
            skid_buff_aw <= S_AXI_AWADDR;
        
        if(skid_buffer_w_wr_en) begin//buffer the data and strobe on a master stall and read request is accepted aswell
            skid_buff_w <= S_AXI_WDATA;
            skid_buff_wstr <= S_AXI_WSTRB;
        end
        
        //write has been done, assert valid signal until master asserts ready
        if(s_axil_regmap_wr_if.wr_en)
            S_AXI_BVALID <= 1'b1;
        else if (S_AXI_BREADY)
            S_AXI_BVALID <= 1'b0;
    end
end


//-------------------------------------------------------------
//Regmap memory interface--------------------------------------
//-------------------------------------------------------------

logic [C_S_AXI_ADDR_WDT-1:0]   s_axil_regmap_rd_if_rd_addr_q;
logic                          s_axil_regmap_rd_if_rd_en_q;
logic [C_S_AXI_ADDR_WDT-1:0]   s_axil_regmap_wr_if_wr_addr_q;
logic [C_REGMAP_DATA_WDT-1:0]  s_axil_regmap_wr_if_wr_data_q;
logic [C_S_AXI_STRB_WDT-1:0]   s_axil_regmap_wr_if_wr_strb_q;
logic                          s_axil_regmap_wr_if_wr_en_q;
logic [2*C_S_AXI_ADDR_WDT + C_REGMAP_DATA_WDT + C_S_AXI_STRB_WDT + 2-1:0] s_axil_2regmap_q;
logic [2*C_S_AXI_ADDR_WDT + C_REGMAP_DATA_WDT + C_S_AXI_STRB_WDT + 2-1:0] s_axil_2regmap;

assign s_axil_regmap_rd_if_rd_addr_q = (skid_buffer_ar_rd_en ? skid_buff_ar : S_AXI_ARADDR);
assign s_axil_regmap_rd_if_rd_en_q   = !rd_resp_stall & val_rd_req; //read anytime the read response isnt stalled and valid request is on

assign s_axil_regmap_wr_if_wr_addr_q      = skid_buffer_aw_rd_en ? skid_buff_aw : S_AXI_AWADDR;
assign s_axil_regmap_wr_if_wr_data_q      = skid_buffer_w_rd_en ? skid_buff_w : S_AXI_WDATA;
assign s_axil_regmap_wr_if_wr_strb_q      = skid_buffer_w_rd_en ? skid_buff_wstr : S_AXI_WSTRB;
assign s_axil_regmap_wr_if_wr_en_q        = !wr_resp_stall & val_wr_addr & val_wr_data;

assign S_AXI_RDATA  = skid_buff_r_val ? skid_buff_r : s_axil_regmap_rd_if.rd_data;

always_comb begin : regmap_if_pack_unpack_proc
    s_axil_2regmap_q = {s_axil_regmap_rd_if_rd_addr_q, s_axil_regmap_rd_if_rd_en_q, s_axil_regmap_wr_if_wr_addr_q, s_axil_regmap_wr_if_wr_data_q, s_axil_regmap_wr_if_wr_strb_q, s_axil_regmap_wr_if_wr_en_q};
    
    s_axil_regmap_rd_if.rd_addr  = s_axil_2regmap[1 + C_S_AXI_STRB_WDT + C_REGMAP_DATA_WDT + C_S_AXI_ADDR_WDT + 1 +: C_S_AXI_ADDR_WDT];
    s_axil_regmap_rd_if.rd_en    = s_axil_2regmap[1 + C_S_AXI_STRB_WDT + C_REGMAP_DATA_WDT + C_S_AXI_ADDR_WDT +: 1]; 
    s_axil_regmap_wr_if.wr_addr  = s_axil_2regmap[1 + C_S_AXI_STRB_WDT + C_REGMAP_DATA_WDT +: C_S_AXI_ADDR_WDT];
    s_axil_regmap_wr_if.wr_data  = s_axil_2regmap[1 + C_S_AXI_STRB_WDT +: C_REGMAP_DATA_WDT];
    s_axil_regmap_wr_if.wr_strb  = s_axil_2regmap[1 +: C_S_AXI_STRB_WDT];
    s_axil_regmap_wr_if.wr_en    = s_axil_2regmap[0 +: 1];
end

del_chain //read and write interface delay chain (direction to regmap)
#(
    .IN_WORD_WDT($bits(s_axil_2regmap_q)),
    .DEL_CYC_LEN(C_S_AXI_2REGMAP_DEL_CYC_LEN)
)
s_axil_2regmap_if_del_chain
(
    .clk(S_AXI_ACLK),
    .rst_n(S_AXI_ARESETN),
    .clk_en(1'b1),
    .in_word(s_axil_2regmap_q),
    .in_word_val(),
    .in_word_del(s_axil_2regmap),
    .in_word_val_del()
);

//synthesis translate_off
    
//verify that unaligned read transaction dont happen
always_ff @(posedge S_AXI_ACLK) assert (!(S_AXI_ARADDR[1:0] != 2'b00 & rd_addr_accept) | !S_AXI_ARESETN) else $error("Unaligned reads are not supported in the AXI-Lite slave");

//verify valid regmap response aligns with RVALID
val_rd_resp_regmap: assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) ($rose(rvalid_next_cyc) |-> ##1 $rose(S_AXI_RVALID) & s_axil_regmap_rd_if.rd_val)) 
    else $error("Valid response flag coming from regmap shall align with interface read valid signal!");
    
//verify that if we write to the skid buffer, we eventually read from it aswell
ar_skid_wr_rd_en: assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) ($rose(skid_buffer_ar_wr_en) |-> ##[0:50] !skid_buffer_ar_wr_en ##1 $rose(skid_buffer_ar_rd_en))) 
    else $error("If we write to the address skid buffer we shall read it eventually!");

//verify that skid buffer w/r en signals are one cycle long pulses
skid_wr_en_pulse: assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (skid_buffer_ar_wr_en |-> ##1 !skid_buffer_ar_wr_en)) 
    else $error("The address skid buffer write enable shall be a cycle long pulse");

skid_rd_en_pulse: assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (skid_buffer_ar_rd_en |-> ##1 !skid_buffer_ar_rd_en)) 
    else $error("The address skid buffer read enable shall be a cycle long pulse");

//verify that no transactions hang
axi_rd_hshake: assert property (@(posedge S_AXI_ACLK) disable iff (!S_AXI_ARESETN) (rd_addr_accept |-> ##[1:50] rd_resp_accept)) else
    $error("Read channel transaction appears to be hanged up");
    
//synthesis translate_on

endmodule