`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     pipe_fifo
// Project Name:    Efficient FPGA CNN implementation
// Description:     backpressure FIFO, meant to be placed between two processing pipeline blocks
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import proc_pipe_pckg::*;

module pipe_fifo
#(
    parameter WORD_WDT = 64,
    parameter FIFO_DEPTH = 2**3
)
(
    //clk & reset & enable
    input   logic clk,
    input   logic rst_n,
    //control
    proc_pipe_ctrl_if.proc_prod   upstream_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_prod   downstream_pipe_ctrl_if,
    //data & address
    input  logic [WORD_WDT-1:0] upstream_word,
    input  logic upstream_word_val,
    output logic [WORD_WDT-1:0] downstream_word,
    output logic downstream_word_val

);

logic fifo_wr;
logic fifo_full;
logic fifo_full_q;
logic fifo_rd;
logic fifo_empty;
logic [WORD_WDT-1:0] downstream_word_i;

assign fifo_wr = upstream_word_val & upstream_pipe_ctrl_if.step; //write if we have valid word at input, we are stepping upstream
assign fifo_rd = !downstream_pipe_ctrl_if.stall & !fifo_empty; 
//read if we are not stalled by downstream, fifo is not 
//output is valid if we have just read a word and we are not being stalled
//valid signal may stay asserted for many cycles if fifo is being stalled, but the buffer register in the downstream block 
//shall be stalled as well, so no data duplication shall occur

always_ff @(posedge clk) begin : upstream_step_reg //upstream block is stepped if fifo is not full and it is enabled
    if(!rst_n) begin
        upstream_pipe_ctrl_if.step <= 1'b0;
    end else begin
        upstream_pipe_ctrl_if.step <= !fifo_full_q & upstream_pipe_ctrl_if.en;
    end
end

always_ff @(posedge clk) begin : downstream_word_val_proc
    if(!rst_n) begin
        downstream_word_val <= 1'b0;
    end else begin
        if(!downstream_pipe_ctrl_if.stall) 
            downstream_word_val <= fifo_rd;
    end
end

//-------------------------------------------------------------
//FIFO---------------------------------------------------------
//-------------------------------------------------------------

localparam FIFO_ADDR_WDT = $clog2(FIFO_DEPTH);

//-------------------------------------------------------------
//write channel------------------------------------------------
//-------------------------------------------------------------

logic [FIFO_ADDR_WDT-1:0] fifo_wr_ptr;
logic [FIFO_ADDR_WDT-1:0] fifo_rd_ptr;

assign fifo_full_q = (fifo_rd_ptr + {{(FIFO_ADDR_WDT-1){1'b1}}, 1'b0} == fifo_wr_ptr & fifo_wr & !fifo_rd) | (fifo_rd_ptr + {(FIFO_ADDR_WDT){1'b1}} == fifo_wr_ptr & !fifo_rd);

always_ff @(posedge clk) begin : fifo_full_reg //FIFO will be full in next cycle if rd_ptr - wr_ptr == 2 and new write and no read OR when rd_ptr - wr_ptr == 1 and no read
    if(!rst_n) begin
        fifo_full <= 1'b0;
    end else begin
        fifo_full <= fifo_full_q;
    end
end

always_ff @(posedge clk) begin : fifo_wr_ctrl
    if(!rst_n) begin
        fifo_wr_ptr <= '0;
    end else begin
        if(fifo_wr)
            fifo_wr_ptr <= fifo_wr_ptr + 1;
    end
end

//-------------------------------------------------------------
//memory-------------------------------------------------------
//-------------------------------------------------------------

logic [WORD_WDT-1:0] fifo_mem[FIFO_DEPTH-1:0];

always_ff @(posedge clk) begin : fifo_mem_proc //write first
    if(fifo_wr)
        fifo_mem[fifo_wr_ptr] <= upstream_word;
    if(fifo_rd)
        downstream_word_i <= fifo_mem[fifo_rd_ptr];
end

//-------------------------------------------------------------
//read channel-------------------------------------------------
//-------------------------------------------------------------

assign fifo_empty = fifo_wr_ptr == fifo_rd_ptr;

always_ff @(posedge clk) begin : fifo_rd_ctrl
    if(!rst_n) begin
        fifo_rd_ptr <= '0;
    end else begin
        if(fifo_rd)
            fifo_rd_ptr <= fifo_rd_ptr + 1;
    end
end

//synthesis translate_off

//basic FIFO assertions

always @(posedge clk) assert (!(fifo_wr & fifo_full) | !rst_n) else $error("Cannot write to a full fifo!");

always @(posedge clk) assert (!(fifo_rd & fifo_empty) | !rst_n) else $error("Cannot read from an empty fifo!");

always @(posedge clk) assert (!(fifo_wr & fifo_rd & fifo_rd_ptr === fifo_wr_ptr) | !rst_n) else $error("Cannot write and read from the same FIFO loation!");

//synthesis translate_on

//MUXing
assign downstream_word = downstream_word_val ? downstream_word_i : '0;

endmodule