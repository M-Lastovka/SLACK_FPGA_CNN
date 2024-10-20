`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     axi_if_pckg
// Project Name:    Efficient FPGA CNN implementation
// Description:     package defining the params of the AXI interfaces of the design
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////


package axi_if_pckg;
import arith_pckg::*;

//AXI SLAVE

parameter C_BYTE_WDT = 8;

parameter C_S_TDATA_WDT = 32;  
parameter C_S_TKEEP_WDT = C_S_TDATA_WDT/C_BYTE_WDT;
parameter C_EXT_DATA_WORD_WDT = 16;
parameter C_S_FIFO_WDT = C_S_TDATA_WDT + 1 + $clog2(C_S_TKEEP_WDT+1);
parameter C_S_AXIS_OUT_CYC_LEN = 3;
parameter C_S_AXIS_DONE_CYC_LEN = 2;

//AXI MASTER

parameter C_M_TDATA_WDT = 32;  
parameter C_M_TKEEP_WDT = C_M_TDATA_WDT/C_BYTE_WDT;  
parameter C_M_AXIS_FETCH_CYC_LEN = 3;
parameter C_M_FIFO_WDT = C_M_TDATA_WDT + 1 + C_M_TKEEP_WDT;
parameter C_M_AXIS_DONE_CYC_LEN = 2;

//AXI LITE SLAVE
parameter C_S_AXI_ADDR_WDT = 32;
parameter C_S_AXI_DATA_WDT = 32;
parameter C_S_AXI_STRB_WDT = C_S_AXI_DATA_WDT/C_BYTE_WDT;

parameter C_REGMAP_CMD_CYC_LEN = 2;
parameter C_S_AXI_2REGMAP_DEL_CYC_LEN = 1;
parameter C_S_REGMAP_2AXI_DEL_CYC_LEN = 1;
parameter C_S_AXI_REGMAP_CYC_LEN = C_S_AXI_2REGMAP_DEL_CYC_LEN + C_REGMAP_CMD_CYC_LEN + C_S_REGMAP_2AXI_DEL_CYC_LEN - 1; //cycle latency of regmap read


//conversion between external and internal precision (we add/remove extra frac. bits)
function automatic logic [C_ARITH_WORD_LEN-1:0] conv_ext2int(logic [C_EXT_DATA_WORD_WDT-1:0] data_ext); 
    return {data_ext, {C_ARITH_WORD_LEN-C_EXT_DATA_WORD_WDT{1'b0}}};
endfunction

function automatic logic [C_EXT_DATA_WORD_WDT-1:0] conv_int2ext(logic [C_ARITH_WORD_LEN-1:0] data_int); 
    return data_int[C_ARITH_WORD_LEN-1 -: C_EXT_DATA_WORD_WDT];
endfunction

endpackage