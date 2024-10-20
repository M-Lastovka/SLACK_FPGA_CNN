`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     mmem
// Project Name:    Efficient FPGA CNN implementation
// Description:     Main memory block 
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import proc_pipe_pckg::*;
import mem_pckg::*;

module mmem
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    input  logic mmem_rd_clk_en,
    input  logic mmem_wr_clk_en,
    //control
    output logic mmem_rd_step,
    output logic mmem_wr_step,
    //data & address 
    mem_if.mem   mmem_if
);

generate
    if(C_MMEM_TYPE == STATIC_URAM) begin

        mem_if 
        #(
            .RD_ADDR_WDT(mmem_if.RD_ADDR_WDT),
            .DATA_OUT_WDT(mmem_if.DATA_OUT_WDT),
            .WR_ADDR_WDT(mmem_if.WR_ADDR_WDT),
            .DATA_IN_WDT(mmem_if.DATA_IN_WDT),
            .PIPE_IN_CNT(mmem_if.PIPE_IN_CNT),
            .PIPE_OUT_CNT(mmem_if.PIPE_OUT_CNT)
        ) uram_mem_if (); 

        logic uram_fifo_rd;
        logic uram_fifo_rd_i;
        logic uram_fifo_wr;
        logic mmem_if_rd_en_i;

        logic uram_mem_if_rd_en_q;
        logic [mmem_if.RD_ADDR_WDT-1:0] uram_mem_if_rd_addr_q;
        logic [mmem_if.WR_ADDR_WDT-1:0] uram_mem_if_wr_addr_q;
        logic uram_mem_if_wr_en_q;  
        logic [mmem_if.DATA_IN_WDT-1:0] uram_mem_if_data_in_q;

        localparam C_URAM_RD_IN_PACK_WDT = $bits(uram_mem_if_rd_en_q) + $bits(uram_mem_if_rd_addr_q) + $bits(uram_mem_if_wr_addr_q) + $bits(uram_mem_if_wr_en_q) + $bits(uram_mem_if_data_in_q) + $bits(mmem_if.rd_en);

        logic [C_URAM_RD_IN_PACK_WDT-1:0] uram_in_rd_pack_del;

        //read enable needs to be asserted even if only write is requested
        assign uram_mem_if_rd_en_q   = mmem_if.rd_en & mmem_rd_clk_en | mmem_if.wr_en & mmem_wr_clk_en; 
        assign uram_mem_if_rd_addr_q = mmem_if.rd_addr;
        assign uram_mem_if_wr_addr_q = mmem_if.wr_addr;
        assign uram_mem_if_wr_en_q   = mmem_if.wr_en & mmem_wr_clk_en;
        assign uram_mem_if_data_in_q = mmem_if.data_in;

        del_chain
        #(
            .IN_WORD_WDT (C_URAM_RD_IN_PACK_WDT), 
            .DEL_CYC_LEN (mmem_if.PIPE_IN_CNT)
        )
        uram_in_rd_del_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(mmem_rd_clk_en),
            .in_word({uram_mem_if_rd_en_q, uram_mem_if_rd_addr_q, uram_mem_if_wr_addr_q, uram_mem_if_wr_en_q, uram_mem_if_data_in_q, mmem_if.rd_en}),
            .in_word_val(),
            .in_word_del(uram_in_rd_pack_del),
            .in_word_val_del()
        );

        assign mmem_if_rd_en_i     = uram_in_rd_pack_del[0 +: 1];
        assign uram_mem_if.data_in = uram_in_rd_pack_del[1 +: mmem_if.DATA_IN_WDT];
        assign uram_mem_if.wr_en   = uram_in_rd_pack_del[1 + mmem_if.DATA_IN_WDT +: 1];
        assign uram_mem_if.wr_addr = uram_in_rd_pack_del[1 + mmem_if.DATA_IN_WDT + 1 +: mmem_if.WR_ADDR_WDT];
        assign uram_mem_if.rd_addr = uram_in_rd_pack_del[1 + mmem_if.DATA_IN_WDT + 1 + mmem_if.WR_ADDR_WDT +: mmem_if.RD_ADDR_WDT];
        assign uram_mem_if.rd_en   = uram_in_rd_pack_del[1 + mmem_if.DATA_IN_WDT + 1 + mmem_if.WR_ADDR_WDT + mmem_if.RD_ADDR_WDT +: 1];

        uram_mem uram_mmem_insts
        (
            .clk(clk),
            .uram_mem_if(uram_mem_if)
        );

        del_chain
        #(
            .IN_WORD_WDT (1), 
            .DEL_CYC_LEN (C_MMEM_PIPE_OUT_CNT + 2)
        )
        uram_fifo_wr_del_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(1'b1),
            .in_word(mmem_if_rd_en_i & mmem_rd_clk_en), //use the original read enable to filter the unwanted reads
            .in_word_val(),
            .in_word_del(uram_fifo_wr),
            .in_word_val_del()
        );

        del_chain
        #(
            .IN_WORD_WDT (1), 
            .DEL_CYC_LEN (C_MMEM_PIPE_OUT_CNT + 3)
        )
        uram_fifo_rd_del_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(mmem_rd_clk_en),
            .in_word(mmem_if_rd_en_i & mmem_rd_clk_en), //use the original read enable to filter the unwanted reads
            .in_word_val(),
            .in_word_del(uram_fifo_rd_i),
            .in_word_val_del()
        );

        assign uram_fifo_rd = uram_fifo_rd_i & mmem_rd_clk_en;

        fifo
        #(
            .WORD_WDT (mmem_if.DATA_OUT_WDT),
            .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH) //FIFO depth must be larger then the URAM pipeline depth
        )
        fifo_bpress_mmem_uram
        (
            .clk(clk),
            .rst_n(rst_n),
            .in_word(uram_mem_if.data_out),
            .out_word(mmem_if.data_out),
            .fifo_wr(uram_fifo_wr),
            .fifo_full(),
            .fifo_rd(uram_fifo_rd),
            .fifo_empty()
        );

        assign mmem_rd_step = 1'b1;
        assign mmem_wr_step = 1'b1;
    end else if(C_MMEM_TYPE == STATIC_BRAM) begin

        mem_if 
        #(
            .RD_ADDR_WDT(mmem_if.RD_ADDR_WDT),
            .DATA_OUT_WDT(mmem_if.DATA_OUT_WDT),
            .WR_ADDR_WDT(mmem_if.WR_ADDR_WDT),
            .DATA_IN_WDT(mmem_if.DATA_IN_WDT),
            .PIPE_IN_CNT(mmem_if.PIPE_IN_CNT),
            .PIPE_OUT_CNT(mmem_if.PIPE_OUT_CNT)
        ) bram_mem_if (); 

        //read enable needs to be asserted even if only write is requested
        assign bram_mem_if.rd_en   = mmem_if.rd_en; 
        assign bram_mem_if.rd_addr = mmem_if.rd_addr;
        assign bram_mem_if.wr_addr = mmem_if.wr_addr;
        assign bram_mem_if.wr_en   = mmem_if.wr_en;
        assign bram_mem_if.data_in = mmem_if.data_in;
	    assign mmem_if.data_out    = bram_mem_if.data_out;

        bram_simple_dual sys_arr_acc_mem
        (
            .clk(clk),
            .clk_rd_en(mmem_rd_clk_en),
            .clk_wr_en(mmem_wr_clk_en),
            .rst_n(rst_n),
            .bram_mem_if(bram_mem_if)
        );

        assign mmem_rd_step = 1'b1;
        assign mmem_wr_step = 1'b1;
    end
endgenerate

// synthesis translate_off

// synthesis translate_on

endmodule