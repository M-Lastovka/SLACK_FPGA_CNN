`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     mem_pckg
// Project Name:    Efficient FPGA CNN implementation
// Description:     package for the memory blocks
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

interface mem_if //general memory interface
#(
    parameter RD_ADDR_WDT,
    parameter DATA_OUT_WDT,
    parameter WR_ADDR_WDT,
    parameter DATA_IN_WDT,
    parameter PIPE_IN_CNT,
    parameter PIPE_OUT_CNT
);
logic [RD_ADDR_WDT-1:0]  rd_addr;
logic [DATA_OUT_WDT-1:0] data_out;
logic [WR_ADDR_WDT-1:0]  wr_addr;
logic [DATA_IN_WDT-1:0]  data_in;
logic rd_en;
logic wr_en;

modport mem
(
    input  rd_addr,
    output data_out,
    input  wr_addr,
    input  data_in,
    input  rd_en,
    input  wr_en
);

modport mem_ctrl
(
    output  rd_addr,
    input   data_out,
    output  wr_addr,
    output  data_in,
    output  rd_en,
    output  wr_en
);
endinterface

package mem_pckg;

typedef struct
{
    int rd_addr_wdt;
    int d_in_wdt;
    int d_out_wdt;
    int pipe_in_cnt;
    int pipe_out_cnt;
} mem_cfg_t;

endpackage