`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     bram_simple_dual
// Project Name:    Efficient FPGA CNN implementation
// Description:     Generic simple dual port BRAM block, support for input and output pipelining.
//                  Support for asymetric read and write ports
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import mem_pckg::*;

module bram_simple_dual
(
    input  logic clk,
    input  logic clk_wr_en,
    input  logic clk_rd_en,
    input  logic rst_n,
    mem_if.mem   bram_mem_if
);

localparam C_BRAM_RD_IN_PACK_WDT = bram_mem_if.RD_ADDR_WDT+1;
localparam C_BRAM_WR_IN_PACK_WDT = bram_mem_if.WR_ADDR_WDT+bram_mem_if.DATA_IN_WDT+1;

(*ram_style = "block" *)
logic [bram_mem_if.DATA_OUT_WDT-1:0] mem[ (1<<bram_mem_if.RD_ADDR_WDT)-1:0];
logic [bram_mem_if.DATA_OUT_WDT-1:0] d_out_i;

logic [C_BRAM_RD_IN_PACK_WDT-1:0] bram_in_rd_pack;
logic [C_BRAM_RD_IN_PACK_WDT-1:0] bram_in_rd_pack_del;
logic [C_BRAM_WR_IN_PACK_WDT-1:0] bram_in_wr_pack;
logic [C_BRAM_WR_IN_PACK_WDT-1:0] bram_in_wr_pack_del;
logic [bram_mem_if.RD_ADDR_WDT-1:0] rd_addr_i;
logic [bram_mem_if.WR_ADDR_WDT-1:0] wr_addr_i;
logic [bram_mem_if.DATA_IN_WDT-1:0] data_in_i;
logic wr_en_i;
logic rd_en_i;
logic[$clog2(bram_mem_if.DATA_OUT_WDT/bram_mem_if.DATA_IN_WDT)-1:0] wr_addr_slice_sel;
logic[bram_mem_if.WR_ADDR_WDT-$clog2(bram_mem_if.DATA_OUT_WDT/bram_mem_if.DATA_IN_WDT)-1:0] wr_addr_line;

always_comb begin : pack_unpack_bram_in
    bram_in_rd_pack[0 +: 1] = bram_mem_if.rd_en;
    bram_in_rd_pack[1 +: bram_mem_if.RD_ADDR_WDT] = bram_mem_if.rd_addr;

    bram_in_wr_pack[0 +: 1] = bram_mem_if.wr_en;
    bram_in_wr_pack[1 +: bram_mem_if.WR_ADDR_WDT] = bram_mem_if.wr_addr;
    bram_in_wr_pack[1 + bram_mem_if.WR_ADDR_WDT +: bram_mem_if.DATA_IN_WDT] = bram_mem_if.data_in;

    rd_en_i   = bram_in_rd_pack_del[0];
    rd_addr_i = bram_in_rd_pack_del[1 +: bram_mem_if.RD_ADDR_WDT];
    
    wr_en_i   = bram_in_wr_pack_del[0];
    wr_addr_i = bram_in_wr_pack_del[1 +: bram_mem_if.WR_ADDR_WDT];
    data_in_i = bram_in_wr_pack_del[1 + bram_mem_if.WR_ADDR_WDT +: bram_mem_if.DATA_IN_WDT];
end

del_chain
#(
    .IN_WORD_WDT (C_BRAM_RD_IN_PACK_WDT), 
    .DEL_CYC_LEN (bram_mem_if.PIPE_IN_CNT)
)
bram_simple_dual_in_rd_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_rd_en),
    .in_word(bram_in_rd_pack),
    .in_word_val(),
    .in_word_del(bram_in_rd_pack_del),
    .in_word_val_del()
);

del_chain
#(
    .IN_WORD_WDT (C_BRAM_WR_IN_PACK_WDT), 
    .DEL_CYC_LEN (bram_mem_if.PIPE_IN_CNT)
)
bram_simple_dual_in_wr_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_wr_en),
    .in_word(bram_in_wr_pack),
    .in_word_val(),
    .in_word_del(bram_in_wr_pack_del),
    .in_word_val_del()
);

generate
    if(bram_mem_if.WR_ADDR_WDT == bram_mem_if.RD_ADDR_WDT) begin : mem_with_slice_select
        //divide the write address
        assign wr_addr_line = wr_addr_i;
        assign wr_addr_slice_sel = 0;

        always_ff @(posedge clk) begin : bram_simple_dual_wr_proc
            if(clk_wr_en) begin
                if(wr_en_i)
                    for(int i = 0; i < bram_mem_if.DATA_OUT_WDT/bram_mem_if.DATA_IN_WDT; i++)
                        if(wr_addr_slice_sel == i)
                            mem[wr_addr_line][i*bram_mem_if.DATA_IN_WDT +: bram_mem_if.DATA_IN_WDT] <= data_in_i;
            end
        end
    end else begin : mem_without_slice_select
        always_ff @(posedge clk) begin : bram_simple_dual_wr_proc
            if(clk_wr_en) begin
                if(wr_en_i)
                    mem[wr_addr_i] <= data_in_i;
            end
        end
    end
endgenerate

always_ff @(posedge clk) begin : bram_simple_dual_rd_proc
    if(clk_rd_en) begin
        if(rd_en_i) begin
            d_out_i <= mem[rd_addr_i];
        end
    end
end

del_chain
#(
    .IN_WORD_WDT (bram_mem_if.DATA_OUT_WDT), 
    .DEL_CYC_LEN (bram_mem_if.PIPE_OUT_CNT)
)
bram_simple_dual_out_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_rd_en),
    .in_word(d_out_i),
    .in_word_val(),
    .in_word_del(bram_mem_if.data_out),
    .in_word_val_del()
);

//synthesis translate_off

initial begin
    assert(((bram_mem_if.DATA_OUT_WDT/bram_mem_if.DATA_IN_WDT) & (bram_mem_if.DATA_OUT_WDT/bram_mem_if.DATA_IN_WDT-1)) == 0) else $fatal (1, "Ratio of bram_mem_if.DATA_OUT_WDT and bram_mem_if.DATA_IN_WDT shall be a power of 2!");
        assert(((bram_mem_if.WR_ADDR_WDT - bram_mem_if.RD_ADDR_WDT == $clog2(bram_mem_if.DATA_OUT_WDT/bram_mem_if.DATA_IN_WDT)) & (bram_mem_if.DATA_OUT_WDT/bram_mem_if.DATA_IN_WDT-1)) == 0) else $fatal (1, "Write and Read address width not corresponding to in/out data width!");
end

//synthesis translate_on

endmodule