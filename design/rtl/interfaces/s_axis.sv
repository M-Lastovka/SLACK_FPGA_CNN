`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     s_axis
// Project Name:    Efficient FPGA CNN implementation
// Description:     AXI-Stream Slave, implements TVALID, TREADY, TDATA, TLAST and TKEEP.
//                  After the Rx logic, the data is written to a FIFO and from there
//                  fed into a stream width converted, to adjust the bus width to the
//                  to the internal memory width.
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import axi_if_pckg::*;
import proc_pipe_pckg::*;

module s_axis
(
    //clocks and resets
    input  S_AXIS_ACLK,
    input  S_AXIS_ARESETN,
    //control
    input  logic [C_S_TDATA_WDT-1:0]  S_AXIS_TDATA,
    input  logic [C_S_TKEEP_WDT-1:0]  S_AXIS_TKEEP,
    input  logic S_AXIS_TLAST,
    input  logic S_AXIS_TVALID,	
    output logic S_AXIS_TREADY,
    proc_pipe_ctrl_if.proc_block s_axis_pipe_ctrl_if,
    block_ctrl_if.slave          s_axis_ctrl,
    input  logic [C_CONV_PARAM_WDT-1:0] stream_in_padding,
    //data & address
    output pipe_data_vect_t  s_axis_data_out
);

    logic s_axis_clk_en;
    assign s_axis_clk_en = s_axis_pipe_ctrl_if.step; //aplies only to the read channel
    assign s_axis_pipe_ctrl_if.stall = 1'b0; //stall of the external master is handled through the AXIS handshaking

    logic s_axis_tready_q;
    logic s_axis_tvalid_q;
    logic s_axis_tlast_q;
    logic s_axis_busy;
    logic s_axis_ctrl_done;
    logic [C_S_TKEEP_WDT-1:0] s_axis_tkeep_q;
    logic [C_S_TKEEP_WDT-1:0] s_axis_tkeep_q_inv;
    logic [C_S_TDATA_WDT-1:0] s_axis_tdata_q;
    logic [C_S_TDATA_WDT-1:0] s_axis_tdata_mask;
    logic [$clog2(C_S_TKEEP_WDT+1)-1:0] s_axis_tdata_val_bytes_q;

    logic skid_buff_en;
    logic [C_S_TDATA_WDT-1:0] skid_buff_tdata;
    logic [C_S_TKEEP_WDT-1:0] skid_buff_tkeep;
    logic skid_buff_tlast;
    logic skid_buff_tvalid;

    logic [C_S_TDATA_WDT-1:0] s_axis_tdata;
    logic [$clog2(C_S_TKEEP_WDT+1)-1:0] s_axis_tdata_val_bytes;
    logic s_axis_tlast;

    logic [C_S_FIFO_WDT-1:0] s_fifo_in_word;
    logic [C_S_FIFO_WDT-1:0] s_fifo_out_word;
    logic s_fifo_wr;
    logic s_fifo_full;
    logic s_fifo_rd;
    logic s_fifo_empty;

    //-------------------------------------------------------------
    //Write channel------------------------------------------------
    //-------------------------------------------------------------

    assign s_axis_tready_q = !s_fifo_full & s_axis_busy; //we are ready to accept a new word if the output FIFO is not full
    assign skid_buff_en = !s_axis_tready_q & S_AXIS_TREADY;

    always_ff @(posedge S_AXIS_ACLK) begin : skid_buffer
        if(!S_AXIS_ARESETN) begin
            S_AXIS_TREADY    <= 1'b0;
            skid_buff_tdata  <= '0;
            skid_buff_tkeep  <= '1;
            skid_buff_tvalid <= 1'b0;
            skid_buff_tlast  <= 1'b0;
            s_axis_busy      <= 1'b0;
            s_axis_ctrl_done <= 1'b0;
        end else begin
            S_AXIS_TREADY    <= s_axis_tready_q;
            if(!s_axis_busy)
                s_axis_busy      <= s_axis_ctrl.start & s_axis_pipe_ctrl_if.en;
            else
                s_axis_busy      <= !(S_AXIS_TVALID & S_AXIS_TLAST & S_AXIS_TREADY);
            s_axis_ctrl_done     <= S_AXIS_TVALID & S_AXIS_TLAST & S_AXIS_TREADY;
            if(skid_buff_en) begin
                skid_buff_tdata  <= S_AXIS_TDATA;
                skid_buff_tkeep  <= S_AXIS_TKEEP;
                skid_buff_tvalid <= S_AXIS_TVALID;
                skid_buff_tlast  <= S_AXIS_TLAST;
            end
        end
    end

    always_comb begin : skid_mux
        //read the skid buffer if we are recovering from a stall, else read the interface 
        s_axis_tvalid_q        = (s_axis_tready_q & !S_AXIS_TREADY) ? skid_buff_tvalid : S_AXIS_TVALID;
        s_axis_tlast_q         = (s_axis_tready_q & !S_AXIS_TREADY) ? skid_buff_tlast  : S_AXIS_TLAST;
        s_axis_tkeep_q         = (s_axis_tready_q & !S_AXIS_TREADY) ? skid_buff_tkeep  : S_AXIS_TKEEP;
        s_axis_tdata_q         = (s_axis_tready_q & !S_AXIS_TREADY) ? skid_buff_tdata  : S_AXIS_TDATA;
    end

    always_comb begin : tkeep_mask_val_bytes
        s_axis_tdata_mask = s_axis_tdata_q;
        foreach(s_axis_tkeep_q[i])
            if(!s_axis_tkeep_q[i])
                s_axis_tdata_mask[i*C_BYTE_WDT +: C_BYTE_WDT] = '0;
    end

    assign s_axis_tkeep_q_inv = ~s_axis_tkeep_q;

    generate
        if(C_S_TKEEP_WDT == 1) begin
            assign s_axis_tdata_val_bytes_q = s_axis_tkeep_q;
        end else begin
            lead_zero_cnt  //count the number of valid bytes
            #(
                .IN_WORD_WDT(C_S_TKEEP_WDT/2),
                .OUT_WORD_WDT() 
            ) 
            s_axis_lead_zero_cnt
            (
                .in_word_lhs(s_axis_tkeep_q_inv[C_S_TKEEP_WDT-1-:C_S_TKEEP_WDT/2]),
                .in_word_rhs(s_axis_tkeep_q_inv[0+:C_S_TKEEP_WDT/2]),
                .out_word(s_axis_tdata_val_bytes_q)
            );
        end
    endgenerate

    always_comb begin //pack and unpack fifo word
        s_fifo_in_word = {s_axis_tdata_mask, s_axis_tdata_val_bytes_q, s_axis_tlast_q};
        
        s_axis_tlast               = s_fifo_out_word[0 +: 1];
        s_axis_tdata_val_bytes     = s_fifo_out_word[1 +: $clog2(C_S_TKEEP_WDT+1)];
        s_axis_tdata               = s_fifo_out_word[1 + $clog2(C_S_TKEEP_WDT+1) +: C_S_TDATA_WDT];
    end

    assign s_fifo_wr = s_axis_tready_q & s_axis_tvalid_q;

    fifo
    #(
        .WORD_WDT (C_S_FIFO_WDT),
        .FIFO_DEPTH(C_BPRESS_FIFO_DEPTH)
    )
    fifo_bpress_s_axis
    (
        .clk(S_AXIS_ACLK),
        .rst_n(S_AXIS_ARESETN),
        .in_word(s_fifo_in_word),
        .out_word(s_fifo_out_word),
        .fifo_wr(s_fifo_wr),
        .fifo_full(s_fifo_full),
        .fifo_rd(s_fifo_rd),
        .fifo_empty(s_fifo_empty)
    );

    //-------------------------------------------------------------
    //Read channel------------------------------------------------
    //-------------------------------------------------------------

    logic conv_in_word_valid;
    logic conv_in_word_ready;
    logic conv_out_word_valid;
    logic conv_out_word_ready;
    logic conv_out_word_last;
    logic [C_S_TDATA_WDT-1:0] conv_in_word;
    logic [C_VECT_SIZE*C_EXT_DATA_WORD_WDT-1:0] conv_out_word;
    logic [C_VECT_SIZE*C_EXT_DATA_WORD_WDT-1:0] conv_out_word_i;
    logic [$clog2(C_VECT_SIZE*C_EXT_DATA_WORD_WDT+1)-1:0] conv_out_word_req_wdt;
    pipe_data_vect_t s_axis_data_out_q;
    logic [$clog2(C_S_TDATA_WDT+1)-1:0] conv_in_word_val_bits;
    logic s_fifo_n_empty_pulse;
    logic conv_in_word_valid_q;

    always_ff @(posedge S_AXIS_ACLK) begin : m_fifo_n_empty_proc
        if(!S_AXIS_ARESETN) begin
            s_fifo_n_empty_pulse <= 1'b0;
        end else begin
            s_fifo_n_empty_pulse <= s_fifo_empty & s_fifo_wr; //generate pulse when FIFO just became non-empty
        end
    end

    assign s_fifo_rd = (conv_in_word_ready & conv_in_word_valid & !s_fifo_empty) | ((!conv_in_word_valid | conv_in_word_ready) & s_fifo_n_empty_pulse); 
    assign conv_in_word_valid_q = s_fifo_rd;
    assign conv_in_word = {<<C_EXT_DATA_WORD_WDT{s_axis_tdata}}; //switch word order
    assign conv_in_word_val_bits = s_axis_tdata_val_bytes*C_BYTE_WDT;
    assign conv_out_word_req_wdt = $bits(conv_out_word) - stream_in_padding*C_EXT_DATA_WORD_WDT; //padding bits will be added to the output word later

    always_ff @(posedge S_AXIS_ACLK) begin : conv_in_valid_reg //word is valid immediately after read
        if(!S_AXIS_ARESETN) begin
            conv_in_word_valid <= 1'b0;
        end else begin
            if(s_axis_clk_en) begin
                if(!conv_in_word_valid | conv_in_word_ready)
                    conv_in_word_valid <= conv_in_word_valid_q;
            end
        end
    end

    stream_wdt_conv //convert stream of S_AXIS words to vector width
    #(
        .IN_WORD_WDT(C_S_TDATA_WDT),
        .OUT_WORD_WDT(C_VECT_SIZE*C_EXT_DATA_WORD_WDT)
    )
    stream_wdt_conv_s_axis
    (
        .clk(S_AXIS_ACLK),
        .rst_n(S_AXIS_ARESETN),
        .clk_en(s_axis_clk_en),
        .in_word_valid(conv_in_word_valid),
        .in_word_ready(conv_in_word_ready),
        .in_word_last(s_axis_tlast),
        .in_word_val_bits(conv_in_word_val_bits),
        .out_word_req_wdt(conv_out_word_req_wdt),
        .out_word_valid(conv_out_word_valid),
        .out_word_ready(conv_out_word_ready),
        .out_word_last(conv_out_word_last),
        .out_word_val_bits(),
        .in_word(conv_in_word),
        .out_word(conv_out_word)
    );

    assign conv_out_word_ready = s_axis_clk_en; //we are ready to read as long as we are not stalled
    assign conv_out_word_i = {<<C_EXT_DATA_WORD_WDT{conv_out_word}}; //switch word order

    //unpack the converted stream into vector of values, add padding if needed
    always_comb begin : unpack_data_pipe_vect
        s_axis_data_out_q.data_vect_type  = TYPE_DATA;
        s_axis_data_out_q.data_vect_val = conv_out_word_valid & conv_out_word_ready;
        if(s_axis_data_out_q.data_vect_val) begin
            s_axis_data_out_q.data_vect_words = '0;
            foreach(s_axis_data_out_q.data_vect_words[i])
                if(i >= stream_in_padding)
                    s_axis_data_out_q.data_vect_words[i] = conv_ext2int(conv_out_word_i[i*C_EXT_DATA_WORD_WDT +: C_EXT_DATA_WORD_WDT]); //convert external to internal word (add fractional bits)
                else
                    s_axis_data_out_q.data_vect_words[i] = '0; 
            s_axis_data_out_q.data_vect_last  = conv_out_word_last;
        end else begin
            s_axis_data_out_q.data_vect_words = '0;
            s_axis_data_out_q.data_vect_last  = 1'b0;
        end
    end
    
    del_chain
    #(
        .IN_WORD_WDT(C_PIPE_DATA_VECT_WDT),
        .DEL_CYC_LEN(C_S_AXIS_OUT_CYC_LEN)
    )
    s_axis_out_del_chain
    (
        .clk(S_AXIS_ACLK),
        .rst_n(S_AXIS_ARESETN),
        .clk_en(s_axis_clk_en),
        .in_word(s_axis_data_out_q),
        .in_word_val(),
        .in_word_del(s_axis_data_out),
        .in_word_val_del()
    );

    del_chain //done delay chain
    #(
        .IN_WORD_WDT(1),
        .DEL_CYC_LEN(C_S_AXIS_DONE_CYC_LEN)
    )
    S_axis_done_del_chain
    (
        .clk(S_AXIS_ACLK),
        .rst_n(S_AXIS_ARESETN),
        .clk_en(1'b1),
        .in_word(s_axis_ctrl_done),
        .in_word_val(),
        .in_word_del(s_axis_ctrl.done),
        .in_word_val_del()
    );

    // synthesis translate_off
    always @(posedge S_AXIS_ACLK) assert (!((s_axis_tkeep_q + 1) & s_axis_tkeep_q === 0) | !s_axis_tvalid_q | !S_AXIS_ARESETN)  else $error("KEEP signal shall be uninterrupted stream of ones and then uninterrupted stream of zeros!");

    // synthesis translate_on

endmodule