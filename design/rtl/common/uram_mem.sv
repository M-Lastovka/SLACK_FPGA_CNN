`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     uram_mem
// Project Name:    Efficient FPGA CNN implementation
// Description:     configurable URAM memory primitive with output pipeline, simple dual port
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import mem_pckg::*;

module uram_mem
(
    input logic clk,
    mem_if.mem  uram_mem_if
);

(* ram_style = "ultra" *)
logic [uram_mem_if.DATA_IN_WDT-1:0] mem[ (1<<uram_mem_if.RD_ADDR_WDT)-1:0];
logic [uram_mem_if.DATA_IN_WDT-1:0] memreg;
logic [uram_mem_if.DATA_IN_WDT-1:0] mem_pipe_stage[uram_mem_if.PIPE_OUT_CNT-1:0];
logic en_pipe_reg[uram_mem_if.PIPE_OUT_CNT:0];

always_ff @(posedge clk) begin : uram_mem_proc //write first
    if(uram_mem_if.rd_en) begin
        if(uram_mem_if.wr_en)
            mem[uram_mem_if.wr_addr] <= uram_mem_if.data_in;
        memreg <= mem[uram_mem_if.rd_addr];
    end
end

generate
    if (uram_mem_if.PIPE_OUT_CNT > 0) begin

        //pipelined enable signal
        always_ff @ (posedge clk) begin : en_pipe_reg_proc
            en_pipe_reg[0] <= uram_mem_if.rd_en;
            for (int i = 0; i < uram_mem_if.PIPE_OUT_CNT; i++)
                en_pipe_reg[i+1] <= en_pipe_reg[i];
        end

        //initial RAM output register
        always_ff @ (posedge clk) begin: init_mem_pipe_stage_proc
            if (en_pipe_reg[0])
                mem_pipe_stage [0] <= memreg;    
        end

        //RAM output pipeline
        always_ff @ (posedge clk) begin : mem_pipe_stage_proc
            for (int i = 0; i < uram_mem_if.PIPE_OUT_CNT-1; i++)
                if (en_pipe_reg[i+1]) 
                    mem_pipe_stage[i+1] <= mem_pipe_stage[i];
        end

        //final output register
        always_ff @ (posedge clk) begin : fin_mem_pipe_stage_proc
            if(en_pipe_reg[uram_mem_if.PIPE_OUT_CNT])
                uram_mem_if.data_out <= mem_pipe_stage[uram_mem_if.PIPE_OUT_CNT-1];
        end
    end else begin
        assign uram_mem_if.data_out = memreg;
    end

endgenerate

//synthesis translate_off

initial begin
    assert((uram_mem_if.DATA_OUT_WDT == uram_mem_if.DATA_IN_WDT) & (uram_mem_if.RD_ADDR_WDT == uram_mem_if.WR_ADDR_WDT)) else $fatal (1, "URAM supports only symmetric read and write ports!");
end

//synthesis translate_on
    
endmodule