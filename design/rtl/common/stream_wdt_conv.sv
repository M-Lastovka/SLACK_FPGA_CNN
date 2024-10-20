`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     stream_wdt_conv
// Project Name:    Efficient FPGA CNN implementation
// Description:     Stream width conversion - converts input words of width N into output words
//                  of width M. The bits that come first will end up at LSB 
//
//                  Width M and N can by adjusted at run time, there is an upper limit for both 
//                  (OUT_WORD_WDT and IN_WORD_WDT respectively)                  
//                  
//                  When N > M then the write side has to supply the number of valid bits in the 
//                  input (counting from LSB)
//                  When N <= M then the read sides is supplied with the number of valid bits in
//                  the current word, and it is assumed that all the input word bits are valid
//
//                  The write side can also supply a last flag to mark the end of a stream, the 
//                  last flag simply propagates to the read port.
//                  
//                  Uses AXI-style handshaking (valid/ready) at input and output ports.
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

module stream_wdt_conv
#(
    parameter IN_WORD_WDT = 64,
    parameter OUT_WORD_WDT = 64
)
(
    //clk & reset & enable
    input   logic clk,
    input   logic clk_en,
    input   logic rst_n,
    //control
    input   logic in_word_valid,
    output  logic in_word_ready,
    input   logic in_word_last,
    input   logic [$clog2(IN_WORD_WDT+1)-1:0] in_word_val_bits, //how many valid bits are being put into the buffer
    output  logic out_word_valid,
    input   logic out_word_ready,
    output  logic out_word_last,
    output  logic [$clog2(OUT_WORD_WDT+1)-1:0] out_word_val_bits, //signals how many valid bits are in the out buffer
    input   logic [$clog2(OUT_WORD_WDT+1)-1:0] out_word_req_wdt,  //how many valid bits constitute a valid output word
    //data & address
    input  logic [IN_WORD_WDT-1:0] in_word,
    output logic [OUT_WORD_WDT-1:0] out_word

);

localparam int WORD_BUFF_WDT = OUT_WORD_WDT + IN_WORD_WDT;

logic [$clog2(WORD_BUFF_WDT + 1)-1:0] buff_cnt; //count of how many valid input word bits are there in the buffer
logic [WORD_BUFF_WDT-1:0] word_buff;
logic [WORD_BUFF_WDT-1:0] in_word_padded;
logic [WORD_BUFF_WDT-1:0] word_buff_l_shift;
logic [WORD_BUFF_WDT-1:0] word_buff_r_shift;
logic [WORD_BUFF_WDT-1:0] word_buff_app_r_shift;
logic in_word_req_gnt;
logic out_word_req_gnt;
logic in_word_last_i;
logic [$clog2(OUT_WORD_WDT+1)-1:0] out_word_req_wdt_i;

assign in_word_req_gnt = in_word_valid & in_word_ready;
assign out_word_req_gnt = out_word_valid & out_word_ready;
assign out_word_valid = buff_cnt >= out_word_req_wdt_i | out_word_last; //valid when there are enough input word bits in the buffer, or when the last word is in the buffer
assign out_word_val_bits = buff_cnt > out_word_req_wdt_i ? out_word_req_wdt_i : buff_cnt;
assign in_word_ready = !out_word_valid | (out_word_req_gnt & (buff_cnt + in_word_val_bits <= WORD_BUFF_WDT)); //ready when there are not enough words in the buffer or if the buffer is full and is being read this cycle

always_comb begin : word_buff_shift_proc
    in_word_padded        = $unsigned(in_word);
    word_buff_l_shift     = (in_word_padded << buff_cnt) | word_buff; //left shift - append new valid word
    word_buff_app_r_shift = (in_word_padded << (buff_cnt - out_word_req_wdt_i)) | (word_buff >> out_word_req_wdt_i);//word_buff_l_shift >> out_word_req_wdt_i;  //right shift - shift out the output word, append new valid word
    word_buff_r_shift     = (word_buff >> out_word_req_wdt_i); //right shift - shift out the output word
end

always_ff @(posedge clk) begin : out_word_req_wdt_reg
    if(!rst_n) begin
        out_word_req_wdt_i <= OUT_WORD_WDT;
    end else begin
        out_word_req_wdt_i <= out_word_req_wdt;
    end
end

always_ff @(posedge clk) begin : out_buffer_reg_proc
    if(!rst_n) begin
        buff_cnt           <= '0;
        word_buff          <= '0;
    end else begin
        if(clk_en) begin
            if(out_word_req_gnt & !in_word_req_gnt)
                word_buff <= word_buff_r_shift;
            else if(out_word_req_gnt & in_word_req_gnt)
                word_buff <= word_buff_app_r_shift;
            else if(in_word_req_gnt)
                word_buff <= word_buff_l_shift;

            if(out_word_req_gnt & out_word_last)
                buff_cnt  <= 0;
            else
                buff_cnt  <= buff_cnt - (out_word_req_gnt ? out_word_req_wdt_i : 0) + (in_word_req_gnt ? in_word_val_bits : 0);
        end
    end
end

assign out_word = word_buff[OUT_WORD_WDT-1:0];

generate
    if(IN_WORD_WDT <= OUT_WORD_WDT) begin

        always_ff @(posedge clk) begin : out_buffer_reg_proc
            if(!rst_n) begin
                out_word_last     <= 1'b0;
            end else begin
                if(clk_en) begin
                    if(!out_word_last)
                        out_word_last <= in_word_last & in_word_req_gnt;
                    else if(out_word_last)
                        out_word_last <= !out_word_req_gnt;
                end
            end
        end

        assign in_word_last_i = 1'b0;

    end else begin

        always_ff @(posedge clk) begin : out_buffer_reg_proc
            if(!rst_n) begin
                in_word_last_i    <= 1'b0;
            end else begin
                if(clk_en) begin
                    if(!in_word_last_i)
                        in_word_last_i <= in_word_last & in_word_req_gnt;
                    else if(in_word_last_i)
                        in_word_last_i <= !out_word_last;
                end
            end
        end

        assign out_word_last = in_word_last_i & buff_cnt <= out_word_req_wdt_i;
    end
endgenerate

//synthesis translate_off

//synthesis translate_on

endmodule