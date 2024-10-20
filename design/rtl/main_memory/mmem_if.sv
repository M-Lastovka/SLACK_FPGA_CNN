`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     mmem_if
// Project Name:    Efficient FPGA CNN implementation
// Description:     Main memory block interface - services reads
//                  and writes requests by reading and writing to FIFOs and then the memory
//                  itself.
// 
//                  If the memory is a statically allocated block of FPGA memory resources the 
//                  read and write latency will be deterministic and constant. 
//                  If the memory is a cache connected to off-chip DRAM, then the read and write
//                  commands can be stalled by the cache when a miss is encountered
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

import arith_pckg::*;
import proc_pipe_pckg::*;
import mem_pckg::*;

module mmem_if
(
    //clk & reset & enable
    input  logic clk,
    input  logic rst_n,
    //control
    proc_pipe_ctrl_if.proc_block  mmem_if_rd_cmd_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_block  mmem_if_rd_data_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_block  mmem_if_wr_cmd_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_block  mmem_if_wr_data_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_block  mmem_if_ext_out_pipe_ctrl_if,
    proc_pipe_ctrl_if.proc_block  mmem_if_ext_in_pipe_ctrl_if,
    block_ctrl_if.slave           addr_gen_wr_port_ctrl,
    block_ctrl_if.slave           addr_gen_rd_port_ctrl,
    block_ctrl_if.master          m_axis_ctrl,
    //data & address 
    input  mem_cmd_rd_t     mmem_if_rd_cmd,
    output pipe_data_vect_t mmem_if_rd_data_out,
    input  mem_cmd_wr_t     mmem_if_wr_cmd,
    input  pipe_data_vect_t mmem_if_wr_data_in,
    output pipe_data_vect_t mmem_if_ext_rd_data_out,
    input  pipe_data_vect_t mmem_if_ext_wr_data_in
);

//clock enables, resets
logic mmem_if_rst_n;
logic mmem_if_rd_clk_en;
logic mmem_rd_clk_en;
logic mmem_rd_step;
logic mmem_wr_step;

assign mmem_if_rst_n = !(!rst_n | mmem_if_rd_cmd_pipe_ctrl_if.clear | mmem_if_rd_data_pipe_ctrl_if.clear | mmem_if_wr_cmd_pipe_ctrl_if.clear | mmem_if_wr_data_pipe_ctrl_if.clear);

assign mmem_rd_clk_en = mmem_if_rd_cmd_pipe_ctrl_if.en & 
    ((mmem_if_rd_data_pipe_ctrl_if.en & mmem_if_rd_data_pipe_ctrl_if.step) | 
    (mmem_if_ext_out_pipe_ctrl_if.en & mmem_if_ext_out_pipe_ctrl_if.step)); //step the read port when the read data FIFOs (external or internal) are not stalling
assign mmem_if_rd_clk_en = mmem_rd_clk_en & mmem_rd_step; //step the read channel when read port is not stalling
assign mmem_if_rd_cmd_pipe_ctrl_if.stall = !mmem_rd_step | 
    (!mmem_if_rd_data_pipe_ctrl_if.step & mmem_if_rd_data_pipe_ctrl_if.en) | 
    (!mmem_if_ext_out_pipe_ctrl_if.step & mmem_if_ext_out_pipe_ctrl_if.en); //simply propagate the stall by the main memory or the external interface or the proc pipeline

logic mmem_if_wr_clk_en;
logic mmem_wr_clk_en;

assign mmem_wr_clk_en = (mmem_if_wr_data_pipe_ctrl_if.en | mmem_if_ext_in_pipe_ctrl_if.en) & mmem_if_wr_cmd_pipe_ctrl_if.en; //step the memory write port always
assign mmem_if_wr_clk_en = mmem_wr_clk_en & mmem_wr_step; //step the write channel when the write port is not stalling
assign mmem_if_wr_cmd_pipe_ctrl_if.stall =  !mmem_wr_step | (mmem_if_wr_cmd_i.cmd_wr_en & !mmem_if_wr_data_in_i.data_vect_val); //stall the wr command FIFO if we have valid command but no valid data or the memory is stalling
assign mmem_if_wr_data_pipe_ctrl_if.stall = !mmem_wr_step | (!mmem_if_wr_cmd_i.cmd_wr_en & mmem_if_wr_data_in_i.data_vect_val); //stall the wr data FIFO if we have valid command but no valid data or the memory is stalling

assign mmem_if_ext_in_pipe_ctrl_if.stall = mmem_if_wr_data_pipe_ctrl_if.stall; //the external write port gets stalled the same as the internal one

//-------------------------------------------------------------
//Read chanel--------------------------------------------------
//-------------------------------------------------------------

mem_cmd_rd_t mmem_if_rd_cmd_i;
mem_cmd_rd_t mmem_if_rd_cmd_del_in;
mem_cmd_rd_t mmem_if_rd_cmd_del_out;
logic [C_VECT_WORD_WDT-1:0] mmem_data_out;

//register the read command
always_ff @(posedge clk) begin : mmem_if_rd_port_reg
    if(!mmem_if_rst_n) begin
        mmem_if_rd_cmd_i            <= '0;
        mmem_if_rd_cmd_del_in       <= '0;
        addr_gen_rd_port_ctrl.done  <= 1'b0;
        m_axis_ctrl.start           <= 1'b0;
    end else begin
        if(mmem_if_rd_clk_en) begin
           if(mmem_if_rd_cmd.cmd_rd_en & !mmem_if_rd_cmd.cmd_rd_data_vect_zero_padd & !mmem_if_rd_cmd.cmd_rd_data_vect_neg_inf_padd) //valid request, forward to memory block
               mmem_if_rd_cmd_i <= mmem_if_rd_cmd;
           else  //non-valid request or padded data, forward nothing to memory
               mmem_if_rd_cmd_i <= '0;
           mmem_if_rd_cmd_del_in <= mmem_if_rd_cmd;
           if(!addr_gen_rd_port_ctrl.done) //generate a pulse when the last read request is accepted by external master (only when sink source of read is external)
                addr_gen_rd_port_ctrl.done <= m_axis_ctrl.done;
           else
                addr_gen_rd_port_ctrl.done <= 1'b0;
        end   
    end
end

//delay side-channel and read port mux info while the data is fetched
del_chain 
#(
    .IN_WORD_WDT($bits(mmem_if_rd_cmd_del_in)),
    .DEL_CYC_LEN(C_MMEM_MIN_RD_CYC_LEN)
)
mmem_if_rd_side_ch_del_chain
(
    .clk(clk),
    .rst_n(mmem_if_rst_n),
    .clk_en(mmem_if_rd_clk_en),
    .in_word(mmem_if_rd_cmd_del_in),
    .in_word_val(),
    .in_word_del(mmem_if_rd_cmd_del_out),
    .in_word_val_del()
);

always_comb begin : mmem_if_data_out_mux //put the read data into a data vector

    casez (mmem_if_rd_cmd_del_out.cmd_rd_port_mux)
        INTERN : begin
            if(mmem_if_rd_cmd_del_out.cmd_rd_en) begin
                foreach(mmem_if_rd_data_out.data_vect_words[i])
                    if(mmem_if_rd_cmd_del_out.cmd_rd_data_vect_zero_padd)
                        mmem_if_rd_data_out.data_vect_words[i] = '0;
                    else if(mmem_if_rd_cmd_del_out.cmd_rd_data_vect_neg_inf_padd)
                        mmem_if_rd_data_out.data_vect_words[i] = C_MIN_NEG_VALUE;
                    else
                        mmem_if_rd_data_out.data_vect_words[i] = mmem_data_out[i*C_ARITH_WORD_LEN +: C_ARITH_WORD_LEN];
                mmem_if_rd_data_out.data_vect_val  = mmem_if_rd_cmd_del_out.cmd_rd_en;
                mmem_if_rd_data_out.data_vect_last = mmem_if_rd_cmd_del_out.cmd_rd_data_vect_last;
                mmem_if_rd_data_out.data_vect_type = mmem_if_rd_cmd_del_out.cmd_rd_data_vect_type;
            end else begin
                mmem_if_rd_data_out = C_PIPE_DATA_VECT_RST_VAL;
            end
            mmem_if_ext_rd_data_out = C_PIPE_DATA_VECT_RST_VAL;
        end 
        EXTERN : begin
            if(mmem_if_rd_cmd_del_out.cmd_rd_en) begin
                foreach(mmem_if_ext_rd_data_out.data_vect_words[i])
                    if(mmem_if_rd_cmd_del_out.cmd_rd_data_vect_zero_padd)
                        mmem_if_ext_rd_data_out.data_vect_words[i] = '0;
                    else if(mmem_if_rd_cmd_del_out.cmd_rd_data_vect_neg_inf_padd)
                        mmem_if_ext_rd_data_out.data_vect_words[i] = C_MIN_NEG_VALUE;
                    else
                        mmem_if_ext_rd_data_out.data_vect_words[i] = mmem_data_out[i*C_ARITH_WORD_LEN +: C_ARITH_WORD_LEN];
                mmem_if_ext_rd_data_out.data_vect_val  = mmem_if_rd_cmd_del_out.cmd_rd_en;
                mmem_if_ext_rd_data_out.data_vect_last = mmem_if_rd_cmd_del_out.cmd_rd_data_vect_last;
                mmem_if_ext_rd_data_out.data_vect_type = mmem_if_rd_cmd_del_out.cmd_rd_data_vect_type;
            end else begin
                mmem_if_ext_rd_data_out = C_PIPE_DATA_VECT_RST_VAL;
            end
            mmem_if_rd_data_out = C_PIPE_DATA_VECT_RST_VAL;
        end
        IDLE : begin
            mmem_if_rd_data_out      = C_PIPE_DATA_VECT_RST_VAL;
            mmem_if_ext_rd_data_out  = C_PIPE_DATA_VECT_RST_VAL;
        end
        default: begin
            mmem_if_rd_data_out      = C_PIPE_DATA_VECT_RST_VAL;
            mmem_if_ext_rd_data_out  = C_PIPE_DATA_VECT_RST_VAL;
        end
    endcase
end

//-------------------------------------------------------------
//Write chanel-------------------------------------------------
//-------------------------------------------------------------

logic [C_VECT_WORD_WDT-1:0] mmem_data_in;
mem_cmd_wr_t mmem_if_wr_cmd_i;
pipe_data_vect_t mmem_if_wr_data_in_i;
mem_port_mux_t cmd_wr_port_mux_i;

//register the write command and data
always_ff @(posedge clk) begin : mmem_if_wr_port_reg
    if(!mmem_if_rst_n) begin
        mmem_if_wr_cmd_i            <= '0;
        mmem_if_wr_data_in_i        <= C_PIPE_DATA_VECT_RST_VAL;
        addr_gen_wr_port_ctrl.done  <= 1'b0;
    end else begin
        if(mmem_if_wr_clk_en) begin
            cmd_wr_port_mux_i = mmem_if_wr_cmd_i.cmd_wr_en ? mmem_if_wr_cmd_i.cmd_wr_port_mux : mmem_if_wr_cmd.cmd_wr_port_mux; //at the first command, choose the register input
            casez (cmd_wr_port_mux_i)
                EXTERN : begin
                    mmem_if_wr_cmd_i     <= mmem_if_wr_cmd_pipe_ctrl_if.stall ? mmem_if_wr_cmd_i : mmem_if_wr_cmd;
                    mmem_if_wr_data_in_i <= mmem_if_wr_data_pipe_ctrl_if.stall ? mmem_if_wr_data_in_i : mmem_if_ext_wr_data_in;
                end 
                INTERN : begin
                    mmem_if_wr_cmd_i     <= mmem_if_wr_cmd_pipe_ctrl_if.stall ? mmem_if_wr_cmd_i : mmem_if_wr_cmd;
                    mmem_if_wr_data_in_i <= mmem_if_wr_data_pipe_ctrl_if.stall ? mmem_if_wr_data_in_i : mmem_if_wr_data_in;
                end
                IDLE : begin
                    mmem_if_wr_cmd_i     <= '0;
                    mmem_if_wr_data_in_i <=  C_PIPE_DATA_VECT_RST_VAL;
                end
                default: begin
                    mmem_if_wr_cmd_i     <= '0;
                    mmem_if_wr_data_in_i <=  C_PIPE_DATA_VECT_RST_VAL;
                end
            endcase
            if(!addr_gen_wr_port_ctrl.done) //generate a pulse when the last write request is accepted
                addr_gen_wr_port_ctrl.done <= mmem_if_wr_cmd_i.cmd_wr_data_vect_last & mmem_if_wr_cmd_i.cmd_wr_en & mmem_if_wr_data_in_i.data_vect_val & mmem_wr_step;
            else
                addr_gen_wr_port_ctrl.done <= 1'b0;
        end
    end
end

always_comb begin
    foreach(mmem_if_wr_data_in_i.data_vect_words[i])
        if(mmem_if_wr_data_in_i.data_vect_val)
            mmem_data_in[i*C_ARITH_WORD_LEN +: C_ARITH_WORD_LEN] = mmem_if_wr_data_in_i.data_vect_words[i];
        else
            mmem_data_in[i*C_ARITH_WORD_LEN +: C_ARITH_WORD_LEN] = '0; 
end

//memory and interface instantiation
mem_if 
#(
    .RD_ADDR_WDT(C_MMEM_ADDR_WDT),
    .DATA_OUT_WDT(C_VECT_WORD_WDT),
    .WR_ADDR_WDT(C_MMEM_ADDR_WDT),
    .DATA_IN_WDT(C_VECT_WORD_WDT),
    .PIPE_IN_CNT(C_MMEM_PIPE_IN_CNT),
    .PIPE_OUT_CNT(C_MMEM_PIPE_OUT_CNT)
) mmem_if (); 

always_comb begin : mmem_mux //muxing of the memory inputs/outputs
    mmem_if.rd_en       = mmem_rd_step ? mmem_if_rd_cmd_i.cmd_rd_en : 1'b0;
    mmem_if.rd_addr     = mmem_rd_step ? mmem_if_rd_cmd_i.cmd_rd_addr : '0;
    mmem_data_out       = mmem_if.data_out;
    mmem_if.wr_en       = mmem_wr_step & !mmem_if_wr_cmd_pipe_ctrl_if.stall? mmem_if_wr_cmd_i.cmd_wr_en : 1'b0;
    mmem_if.wr_addr     = mmem_wr_step & !mmem_if_wr_cmd_pipe_ctrl_if.stall ? mmem_if_wr_cmd_i.cmd_wr_addr : '0;
    mmem_if.data_in     = mmem_wr_step & !mmem_if_wr_data_pipe_ctrl_if.stall ? mmem_data_in : '0;
end

mmem mmem_inst
(
    .clk(clk),
    .rst_n(mmem_if_rst_n),
    .mmem_rd_clk_en(mmem_rd_clk_en),
    .mmem_wr_clk_en(mmem_wr_clk_en),
    .mmem_rd_step(mmem_rd_step),
    .mmem_wr_step(mmem_wr_step),
    .mmem_if(mmem_if)
);

// synthesis translate_off

assert property (@(posedge clk) disable iff (!rst_n) ((mmem_if_wr_cmd_i.cmd_wr_en & mmem_if_wr_cmd_i.cmd_wr_data_vect_last) & mmem_if_wr_data_in_i.data_vect_val & (!mmem_if_wr_cmd_pipe_ctrl_if.stall & !mmem_if_wr_data_pipe_ctrl_if.stall & mmem_if_wr_clk_en) |-> 
    ##1 !mmem_if_wr_data_in_i.data_vect_val & !mmem_if_wr_cmd_i.cmd_wr_en)) else $error("After the final write has been accepted the data and command ports shall be deasserted!");

assert property (@(posedge clk) disable iff (!rst_n) ((mmem_if_wr_cmd_i.cmd_wr_en & mmem_if_wr_cmd_i.cmd_wr_data_vect_last) & mmem_if_wr_data_in_i.data_vect_val & (!mmem_if_wr_cmd_pipe_ctrl_if.stall & !mmem_if_wr_data_pipe_ctrl_if.stall & mmem_if_wr_clk_en) |-> 
    mmem_if_wr_data_in_i.data_vect_last)) else $error("On the final write command, the write data shall have the last flag asserted as well");
    
assert property (@(posedge clk) disable iff (!rst_n) ($changed(mmem_if_wr_data_in_i) & $past(mmem_if_wr_data_in_i.data_vect_val, 1) |-> $past(mmem_if_wr_cmd_i.cmd_wr_en, 1))) else $error("Write port data shall change only when address is valid!");
assert property (@(posedge clk) disable iff (!rst_n) ($changed(mmem_if_wr_cmd_i) & $past(mmem_if_wr_cmd_i.cmd_wr_en, 1) |-> $past(mmem_if_wr_data_in_i.data_vect_val, 1))) else $error("Write port address shall change when the data is valid!");

assert property (@(posedge clk) disable iff (!rst_n) (!mmem_wr_step |-> $stable(mmem_if_wr_data_in_i) & $stable(mmem_if_wr_cmd_i))) else $error("Write ports shall remain stable if the main memory is not accepting requests!");

assert property (@(posedge clk) disable iff (!rst_n) (!mmem_rd_step |-> $stable(mmem_if_rd_cmd_i) & $stable(mmem_if_rd_cmd_del_in) & $stable(mmem_if_rd_cmd_del_out))) else $error("Read ports shall remain stable if the main memory is not accepting requests!");

//only data are allowed inside write port
always @(posedge clk) assert (!(mmem_if_wr_data_in_i.data_vect_val & mmem_if_wr_data_in_i.data_vect_type != TYPE_DATA) | !rst_n)  else $error("Only moving values shall written to the main memory!");

// synthesis translate_on

endmodule