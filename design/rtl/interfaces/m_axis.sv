`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     m_axis
// Project Name:    Efficient FPGA CNN implementation
// Description:     AXI-Stream Master, implements TVALID, TREADY, TDATA, TLAST and TKEEP.
//                  The data is first converted to appropriate width, then sent to the Tx logic.
//                  In between there is a FIFO.
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import axi_if_pckg::*;
import proc_pipe_pckg::*;

module m_axis
(
    //clocks and resets
    input  M_AXIS_ACLK,
    input  M_AXIS_ARESETN,
    //control
    output  logic [C_M_TDATA_WDT-1:0]  M_AXIS_TDATA,
    output  logic [C_M_TKEEP_WDT-1:0]  M_AXIS_TKEEP,
    output  logic M_AXIS_TLAST,
    output  logic M_AXIS_TVALID,	
    input   logic M_AXIS_TREADY,
    proc_pipe_ctrl_if.proc_block m_axis_pipe_ctrl_if,
    block_ctrl_if.slave          m_axis_ctrl,
    input  logic [C_CONV_PARAM_WDT-1:0] stream_out_padding,
    //data & address
    input  pipe_data_vect_t  m_axis_data_fetch
);

    logic m_axis_clk_en;
    logic m_axis_in_clk_en;
    logic conv_in_word_ready;
    logic conv_in_word_valid;
    logic m_fifo_full;

    assign m_axis_clk_en = !m_fifo_full & m_axis_pipe_ctrl_if.en; //aplies only to the write channel
    assign m_axis_in_clk_en = m_axis_clk_en & (conv_in_word_ready | !conv_in_word_valid); //step the input only if the stream width conversion is not stalling or if it has no valid inputs yet
    assign m_axis_pipe_ctrl_if.stall = !m_axis_in_clk_en; //stall if the FIFO is full or when the stream width converter is stalling

    //-------------------------------------------------------------
    //Write channel------------------------------------------------
    //-------------------------------------------------------------

    logic [C_CONV_PARAM_WDT-1:0] stream_out_padding_del;
    pipe_data_vect_t m_axis_data_fetch_del;
    logic [C_VECT_SIZE*C_EXT_DATA_WORD_WDT-1:0] conv_in_word;
    logic [$clog2(C_VECT_SIZE*C_EXT_DATA_WORD_WDT+1)-1:0] in_word_val_bits;
    logic conv_in_word_last;
    logic conv_out_word_valid;
    logic conv_out_word_ready;
    logic [C_M_TDATA_WDT-1:0] conv_out_word;

    logic [$clog2(C_M_TDATA_WDT+1)-1:0] m_axis_tdata_val_bits;
    logic [$clog2(C_M_TKEEP_WDT+1)-1:0] m_axis_tdata_val_bytes;
    logic [C_M_TDATA_WDT-1:0] m_axis_tdata_q;
    logic [C_M_TKEEP_WDT-1:0] m_axis_tkeep_q;
    logic m_axis_tlast_q;
    logic [C_M_TDATA_WDT-1:0] m_axis_tdata;
    logic [C_M_TKEEP_WDT-1:0] m_axis_tkeep;
    logic [C_M_TKEEP_WDT-1:0] m_axis_tkeep_rev;
    logic m_axis_tlast;

    logic [C_M_FIFO_WDT-1:0] m_fifo_in_word;
    logic [C_M_FIFO_WDT-1:0] m_fifo_out_word;
    logic m_fifo_wr;
    logic m_fifo_rd;
    logic m_fifo_empty;

    del_chain //input delay chain
    #(
        .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
        .DEL_CYC_LEN(C_M_AXIS_FETCH_CYC_LEN)
    )
    m_axis_fetch_del_chain
    (
        .clk(M_AXIS_ACLK),
        .rst_n(M_AXIS_ARESETN),
        .clk_en(m_axis_in_clk_en),
        .in_word(m_axis_data_fetch),
        .in_word_val(),
        .in_word_del(m_axis_data_fetch_del),
        .in_word_val_del()
    );

    del_chain //stream padding delay chain
    #(
        .IN_WORD_WDT($bits(stream_out_padding)),
        .DEL_CYC_LEN(1)
    )
    stream_out_padding_del_chain
    (
        .clk(M_AXIS_ACLK),
        .rst_n(M_AXIS_ARESETN),
        .clk_en(m_axis_in_clk_en),
        .in_word(stream_out_padding),
        .in_word_val(),
        .in_word_del(stream_out_padding_del),
        .in_word_val_del()
    );

    //width conversion
    always_comb begin : stream_wdt_conv_int2ext_mux
        conv_in_word_valid = m_axis_data_fetch_del.data_vect_val;
        if(conv_in_word_valid) begin
            foreach(m_axis_data_fetch_del.data_vect_words[i])
                conv_in_word[i*C_EXT_DATA_WORD_WDT +: C_EXT_DATA_WORD_WDT] = conv_int2ext(m_axis_data_fetch_del.data_vect_words[i]);
            conv_in_word = {<<C_EXT_DATA_WORD_WDT{conv_in_word}}; //switch word order
            conv_in_word_last  = m_axis_data_fetch_del.data_vect_last;
        end else begin
            conv_in_word = '0;
            conv_in_word_last = 1'b0;
        end      
    end

    always_ff @(posedge M_AXIS_ACLK) begin : in_word_val_bits_reg //reg for valid bits : stream output padding - max valid bits = valid bits
        if(!M_AXIS_ARESETN) begin
            in_word_val_bits <= '0;
        end else begin
            in_word_val_bits <= C_VECT_SIZE*C_EXT_DATA_WORD_WDT - stream_out_padding_del*C_EXT_DATA_WORD_WDT;
        end
    end

    stream_wdt_conv //convert stream of vectors to M_AXIS bus width
    #(
        .IN_WORD_WDT(C_VECT_SIZE*C_EXT_DATA_WORD_WDT),
        .OUT_WORD_WDT(C_M_TDATA_WDT)
    )
    stream_wdt_conv_m_axis
    (
        .clk(M_AXIS_ACLK),
        .rst_n(M_AXIS_ARESETN),
        .clk_en(m_axis_clk_en),
        .in_word_valid(conv_in_word_valid),
        .in_word_ready(conv_in_word_ready),
        .in_word_last(conv_in_word_last),
        .in_word_val_bits(in_word_val_bits),
        .out_word_valid(conv_out_word_valid),
        .out_word_ready(conv_out_word_ready),
        .out_word_last(m_axis_tlast_q),
        .out_word_val_bits(m_axis_tdata_val_bits),
        .out_word_req_wdt(C_M_TDATA_WDT),
        .in_word(conv_in_word),
        .out_word(conv_out_word)
    );

    assign m_axis_tdata_q = {<<C_EXT_DATA_WORD_WDT{conv_out_word}}; //switch word order

    assign conv_out_word_ready = !m_fifo_full; //write to FIFO when it is not full
    assign m_fifo_wr = conv_out_word_ready & conv_out_word_valid; //if transfer is accepted, write to FIFO

    always_comb begin : gen_tkeep //generate tkeep based on the number of valid bytes in the converted word
        m_axis_tdata_val_bytes = m_axis_tdata_val_bits/C_BYTE_WDT;
        foreach(m_axis_tkeep_q[i])
            if(i < m_axis_tdata_val_bytes)
                m_axis_tkeep_q[i] = 1'b1;
            else
                m_axis_tkeep_q[i] = 1'b0;
    end

    //pack and unpack the fifo word
    always_comb begin //pack and unpack fifo word
        m_fifo_in_word = {m_axis_tdata_q, m_axis_tkeep_q, m_axis_tlast_q};
        
        m_axis_tlast               = m_fifo_out_word[0 +: 1];
        m_axis_tkeep               = m_fifo_out_word[1 +: C_M_TKEEP_WDT];
        m_axis_tdata               = m_fifo_out_word[1 + C_M_TKEEP_WDT +: C_M_TDATA_WDT];
    end
    
    //FIFO between read and write channel
    fifo
    #(
        .WORD_WDT (C_M_FIFO_WDT),
        .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
    )
    fifo_bpress_m_axis
    (
        .clk(M_AXIS_ACLK),
        .rst_n(M_AXIS_ARESETN),
        .in_word(m_fifo_in_word),
        .out_word(m_fifo_out_word),
        .fifo_wr(m_fifo_wr),
        .fifo_full(m_fifo_full),
        .fifo_rd(m_fifo_rd),
        .fifo_empty(m_fifo_empty)
    );

    //-------------------------------------------------------------
    //Read channel-------------------------------------------------
    //-------------------------------------------------------------

    logic m_axis_tvalid_i;
    logic m_fifo_n_empty_pulse;
    logic m_axis_ctrl_done;
    logic m_axis_busy;
    logic m_fifo_first_read; //until first FIFO read pull all AXIS outputs which are outputs of FIFO to zero

    //read FIFO when a pending beat is about to be accepted or when the FIFO just became non-empty
    assign m_fifo_rd = (((M_AXIS_TREADY & M_AXIS_TVALID) & !m_fifo_empty) | ((!M_AXIS_TVALID | M_AXIS_TREADY) & m_fifo_n_empty_pulse)) & m_axis_busy; 

    del_chain //done delay chain
    #(
        .IN_WORD_WDT(1),
        .DEL_CYC_LEN(C_M_AXIS_DONE_CYC_LEN)
    )
    m_axis_done_del_chain
    (
        .clk(M_AXIS_ACLK),
        .rst_n(M_AXIS_ARESETN),
        .clk_en(1'b1),
        .in_word(m_axis_ctrl_done),
        .in_word_val(),
        .in_word_del(m_axis_ctrl.done),
        .in_word_val_del()
    );
    
    //generate tlast & tvalid
    assign m_axis_tkeep_rev = {<<{m_axis_tkeep}};
    assign m_axis_tvalid_i = m_fifo_rd;
    assign M_AXIS_TKEEP    = m_fifo_first_read ? m_axis_tkeep_rev : '0;
    assign M_AXIS_TDATA    = m_fifo_first_read ? m_axis_tdata : '0;
    assign M_AXIS_TLAST    = m_fifo_first_read ? m_axis_tlast : '0;

    always_ff @(posedge M_AXIS_ACLK) begin : m_axis_ctrl_reg //reg tvalid and tlast signals, gate them if they need to be stalled
        if(!M_AXIS_ARESETN) begin
            M_AXIS_TVALID        <= 1'b0;
            m_axis_busy          <= 1'b0;
            m_axis_ctrl_done     <= 1'b0;
            m_fifo_first_read    <= 1'b0;
            m_fifo_n_empty_pulse <= 1'b0;
        end else begin
            m_fifo_n_empty_pulse <= m_fifo_empty & m_fifo_wr; //generate pulse when FIFO just became non-empty

            if(!m_fifo_first_read & m_fifo_rd)
                m_fifo_first_read <= 1'b1;

            if(!m_axis_busy)
                m_axis_busy <= m_axis_pipe_ctrl_if.en; //keep in busy state always for now
            else
                m_axis_busy <= !(M_AXIS_TVALID & M_AXIS_TREADY & M_AXIS_TLAST);
            m_axis_ctrl_done <= M_AXIS_TVALID & M_AXIS_TREADY & M_AXIS_TLAST;

            if(!M_AXIS_TVALID | M_AXIS_TREADY) begin
                M_AXIS_TVALID <= m_axis_tvalid_i;
            end
        end
    end

    // synthesis translate_off
    assert property (@(posedge M_AXIS_ACLK) disable iff (!M_AXIS_ARESETN) (!m_axis_tlast_q & m_fifo_wr |-> m_axis_tdata_val_bits === C_M_TDATA_WDT)) else $error("Valid bits smaller then full length is only allowed on the last beat!");

    assert property (@(posedge M_AXIS_ACLK) disable iff (!M_AXIS_ARESETN) ($rose(m_fifo_n_empty_pulse) |-> ##1 $fell(m_fifo_n_empty_pulse))) else $error("The signal m_fifo_n_empty_pulse shall be a single cycle pulse!");

    always @(posedge M_AXIS_ACLK) assert (!((m_axis_tkeep + 1) & m_axis_tkeep === 0) | !M_AXIS_ARESETN)  else $error("KEEP signal shall be uninterrupted stream of ones and then uninterrupted stream of zeros!");
    // synthesis translate_on

endmodule