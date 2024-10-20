`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     gen_mem_single
// Project Name:    Efficient FPGA CNN implementation
// Description:     generic memory single port, no asymetric read/write support, configurable rd/wr order
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import mem_pckg::*;

module gen_mem_single
#(
    parameter string MEM_RD_WR_ORDER = "WRITE_FIRST"
)
(
    input  logic clk,
    input  logic clk_en,
    input  logic rst_n,
    mem_if.mem   gen_mem_if
);

localparam C_GEN_MEM_IN_PACK_WDT = gen_mem_if.RD_ADDR_WDT + gen_mem_if.DATA_IN_WDT + 2;

logic [gen_mem_if.DATA_OUT_WDT-1:0] mem[ (1<<gen_mem_if.RD_ADDR_WDT)-1:0];
logic [gen_mem_if.DATA_OUT_WDT-1:0] d_out_i;

logic [C_GEN_MEM_IN_PACK_WDT-1:0] gen_mem_in_pack;
logic [C_GEN_MEM_IN_PACK_WDT-1:0] gen_mem_in_pack_del;
logic [gen_mem_if.RD_ADDR_WDT-1:0] addr_i;
logic [gen_mem_if.DATA_IN_WDT-1:0] data_in_i;
logic wr_en_i;
logic en_i;

always_comb begin : pack_unpack_gen_mem_in
    gen_mem_in_pack = 
    {
        gen_mem_if.rd_en,
        gen_mem_if.rd_addr,
        gen_mem_if.wr_en,
        gen_mem_if.data_in
    };

    data_in_i = gen_mem_in_pack_del[0 +: gen_mem_if.DATA_IN_WDT];
    wr_en_i   = gen_mem_in_pack_del[gen_mem_if.DATA_IN_WDT +: 1];
    addr_i    = gen_mem_in_pack_del[gen_mem_if.DATA_IN_WDT + 1 +: gen_mem_if.RD_ADDR_WDT];
    en_i      = gen_mem_in_pack_del[gen_mem_if.DATA_IN_WDT + 1 + gen_mem_if.RD_ADDR_WDT +: 1];
end

del_chain
#(
    .IN_WORD_WDT (C_GEN_MEM_IN_PACK_WDT), 
    .DEL_CYC_LEN (gen_mem_if.PIPE_IN_CNT)
)
gen_mem_simple_dual_in_rd_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_rd_en),
    .in_word(gen_mem_in_rd_pack),
    .in_word_val(),
    .in_word_del(gen_mem_in_rd_pack_del),
    .in_word_val_del()
);
generate 
    if(MEM_RD_WR_ORDER == "WRITE_FIRST") begin
        
        always_ff @(posedge clk) begin : gen_mem_single_mem_proc //write first
            if(clk_en) begin
                if(en_i) begin
                    if(wr_en_i)
                        mem[addr_i] <= data_in_i;
                    d_out_i <= mem[addr_i];
                end
            end
        end

    end else if(MEM_RD_WR_ORDER == "READ_FIRST") begin

        always_ff @(posedge clk) begin : gen_mem_single_mem_proc //read first
            if(clk_en) begin
                if(en_i) begin
                    d_out_i <= mem[addr_i];
                    if(wr_en_i)
                        mem[addr_i] <= data_in_i;
                end
            end
        end

    end else begin
        assign d_out_i = 'Z;
    end
endgenerate

del_chain
#(
    .IN_WORD_WDT (gen_mem_if.DATA_OUT_WDT), 
    .DEL_CYC_LEN (gen_mem_if.PIPE_OUT_CNT)
)
gen_mem_single_delay_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(d_out_i),
    .in_word_val(),
    .in_word_del(gen_mem_if.d_out),
    .in_word_val_del()
);

//synthesis translate_off

initial begin
    assert(gen_mem_if.DATA_OUT_WDT == gen_mem_if.DATA_IN_WDT & gen_mem_if.RD_ADDR_WDT == gen_mem_if.WR_ADDR_WDT) else $fatal (1, "Asymetric read/write ports not supported");
end

//synthesis translate_on

endmodule