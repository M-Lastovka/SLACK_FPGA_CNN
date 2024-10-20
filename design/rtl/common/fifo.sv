`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     fifo
// Project Name:    Efficient FPGA CNN implementation
// Description:     Simple single clock FIFO with symmetric data word width
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

module fifo
#(
    parameter WORD_WDT = 64,
    parameter FIFO_DEPTH = 2**3
)
(
    //clk & reset & enable
    input   logic clk,
    input   logic rst_n,
    //control
    input  logic fifo_wr,
    output logic fifo_full,
    input  logic fifo_rd,
    output logic fifo_empty,
    //data & address
    input  logic [WORD_WDT-1:0] in_word,
    output logic [WORD_WDT-1:0] out_word

);

localparam FIFO_ADDR_WDT = $clog2(FIFO_DEPTH);

//-------------------------------------------------------------
//write channel------------------------------------------------
//-------------------------------------------------------------

logic [FIFO_ADDR_WDT-1:0] fifo_wr_ptr;
logic [FIFO_ADDR_WDT-1:0] fifo_rd_ptr;

always_ff @(posedge clk) begin : fifo_full_reg //FIFO will be full in next cycle if rd_ptr - wr_ptr == 2 and new write and no read OR when rd_ptr - wr_ptr == 1 and no read
    if(!rst_n) begin
        fifo_full <= 1'b0;
    end else begin
        fifo_full <= (fifo_rd_ptr + {{(FIFO_ADDR_WDT-1){1'b1}}, 1'b0} == fifo_wr_ptr & fifo_wr & !fifo_rd) | (fifo_rd_ptr + {(FIFO_ADDR_WDT){1'b1}} == fifo_wr_ptr & !fifo_rd);
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
//FIFO---------------------------------------------------------
//-------------------------------------------------------------

logic [WORD_WDT-1:0] fifo_mem[FIFO_DEPTH-1:0];

always_ff @(posedge clk) begin : fifo_mem_proc //write first
    if(fifo_wr)
        fifo_mem[fifo_wr_ptr] <= in_word;
    if(fifo_rd)
        out_word <= fifo_mem[fifo_rd_ptr];
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

endmodule