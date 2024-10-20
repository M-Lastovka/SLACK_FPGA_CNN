`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     perf_cnt_pckg
// Project Name:    Efficient FPGA CNN implementation
// Description:     package for defining the performance counters
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

package perf_cnt_pckg;
import regmap_reg_pckg::*;

parameter C_PERF_CNT_WDT = 48;
parameter C_PERF_CNT_WORD_CNT = 3;
parameter C_PERF_CNT_CNT = ((C_PERF_CACHE_STALL_UH_REG_ADDR - C_PERF_RUN_CTRL_REG_ADDR)/4+1)/C_PERF_CNT_WORD_CNT;

parameter C_PERF_RUN_OFFSET = 0;
parameter C_PERF_COMP_OFFSET = 1;
parameter C_PERF_STREAM_C2H_OFFSET = 2;
parameter C_PERF_STREAM_H2C_OFFSET = 3;
parameter C_PERF_CACHE_STALL_OFFSET = 4;

endpackage