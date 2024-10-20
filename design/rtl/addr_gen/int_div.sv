`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     int_div
// Project Name:    Efficient FPGA CNN implementation
// Description:     Integer division using non-restoring algorithm, fully pipelined
//                  Given dividend d_end and divisor d_or it computes d_end = res_quot*d_or + res_rem
//
//                  The division unit does not provide any overflow/division by zero flags, but it
//                  does have assertions which check the input operands for validity
//           
//                  We can also adjust how many bits are computed in each pipeline stage, 
//                  i.e. how many computation stages are between registers. Bits per cycle
//                  has to divide computation stages
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////

module int_div
#(
    parameter D_END_WORD_WDT  = 32,
    parameter D_QUOT_WORD_WDT = 16,
    parameter D_QUOT_BITS_PER_CYCLE = 2,
    parameter D_OR_WORD_WDT   = D_END_WORD_WDT - D_QUOT_WORD_WDT + 1
)
(
    input  logic clk,
    input  logic rst_n,
    input  logic clk_en,
    input  logic [D_END_WORD_WDT-1:0] op_d_end,
    input  logic [D_OR_WORD_WDT-1:0]  op_d_or,
    input  logic op_val,
    output logic [D_QUOT_WORD_WDT-1:0]  res_quot,
    output logic [D_QUOT_WORD_WDT-1:0]  res_rem,
    output logic res_val
);

localparam DIV_STAGE_CNT  = D_QUOT_WORD_WDT;
localparam PIPE_STAGE_CNT = DIV_STAGE_CNT / D_QUOT_BITS_PER_CYCLE;

logic [D_END_WORD_WDT-1:0] p_rem   [DIV_STAGE_CNT-1:0]; //partial remainder stages
logic [D_OR_WORD_WDT-1:0]  d_or_i  [DIV_STAGE_CNT-1:0]; //partial remainder stages
logic [D_OR_WORD_WDT-1:0]  p_rem_q [DIV_STAGE_CNT-1:0];
logic [DIV_STAGE_CNT-1:0]  quot_bit; //new quotient bit
logic [D_OR_WORD_WDT-1:0]  res_rem_q;
logic [D_OR_WORD_WDT-1:0]  res_rem_ext_q;
logic [D_QUOT_WORD_WDT-1:0] res_quot_i;

always_ff @(posedge clk) begin : div_pipeline_proc //division pipeline
    if(!rst_n) begin
        for(int i = D_QUOT_BITS_PER_CYCLE-1; i < DIV_STAGE_CNT; i += D_QUOT_BITS_PER_CYCLE) begin
            p_rem[i]    <= '0;
            d_or_i[i]   <= '0;
            quot_bit[i] <= 1'b0;
        end
    end else begin
        if(clk_en) begin
            for(int i = 0; i < DIV_STAGE_CNT; i++) begin
                if((i + 1) % D_QUOT_BITS_PER_CYCLE == 0) begin //register write stage
                    if(i == 0) begin //start of pipeline
                        if(op_val) begin
                            p_rem_q[0]   = op_d_end[D_END_WORD_WDT-1 -: D_OR_WORD_WDT] - op_d_or;
                            p_rem[0]    <= {p_rem_q[0], op_d_end[0 +: D_END_WORD_WDT - D_OR_WORD_WDT]} << 1;
                            quot_bit[0] <= !p_rem_q[0][D_OR_WORD_WDT-1];
                            d_or_i[0]   <= op_d_or;
                        end else begin //if input is not valid, propagate zeros
                            p_rem[0]    <= '0;
                            quot_bit[0] <= 1'b0;
                            d_or_i[0]   <= 1;
                        end
                    end else begin
                        if(quot_bit[i-1])
                            p_rem_q[i]   = p_rem[i-1][D_END_WORD_WDT-1 -: D_OR_WORD_WDT] - d_or_i[i-1];
                        else
                            p_rem_q[i]   = p_rem[i-1][D_END_WORD_WDT-1 -: D_OR_WORD_WDT] + d_or_i[i-1];
                        p_rem[i]    <= {p_rem_q[i], p_rem[i-1][0 +: D_END_WORD_WDT - D_OR_WORD_WDT]} << 1;
                        quot_bit[i] <= !p_rem_q[i][D_OR_WORD_WDT-1];
                        d_or_i[i]   <= d_or_i[i-1];
                    end
                end else begin //combinational stage
                    if(i == 0) begin //start of pipeline
                        if(op_val) begin
                            p_rem_q[0]   = op_d_end[D_END_WORD_WDT-1 -: D_OR_WORD_WDT] - op_d_or;
                            p_rem[0]     = {p_rem_q[0], op_d_end[0 +: D_END_WORD_WDT - D_OR_WORD_WDT]} << 1;
                            quot_bit[0]  = !p_rem_q[0][D_OR_WORD_WDT-1];
                            d_or_i[0]    = op_d_or;
                        end else begin //if input is not valid, propagate zeros
                            p_rem[0]     = '0;
                            quot_bit[0]  = 1'b0;
                            d_or_i[0]    = 1;
                        end
                    end else begin
                        if(quot_bit[i-1])
                            p_rem_q[i]   = p_rem[i-1][D_END_WORD_WDT-1 -: D_OR_WORD_WDT] - d_or_i[i-1];
                        else
                            p_rem_q[i]   = p_rem[i-1][D_END_WORD_WDT-1 -: D_OR_WORD_WDT] + d_or_i[i-1];
                        p_rem[i]     = {p_rem_q[i], p_rem[i-1][0 +: D_END_WORD_WDT - D_OR_WORD_WDT]} << 1;
                        quot_bit[i]  = !p_rem_q[i][D_OR_WORD_WDT-1];
                        d_or_i[i]    = d_or_i[i-1];
                    end
                end  
            end
        end
    end
end

always_ff @(posedge clk) begin : corr_rem_proc //restore remainder if needed
    if(!rst_n) begin
        res_rem <= '0;
    end else begin
        if(clk_en) begin
            res_rem_ext_q = $signed(p_rem[DIV_STAGE_CNT-1][D_END_WORD_WDT-1 -: D_OR_WORD_WDT-1]);
            if(quot_bit[DIV_STAGE_CNT-1]) begin
                res_rem_q = res_rem_ext_q;
            end else begin //restore remainder
                res_rem_q = res_rem_ext_q + d_or_i[DIV_STAGE_CNT-1];
            end
            res_rem  <= res_rem_q[0 +: D_QUOT_WORD_WDT];
        end
    end
end

logic [D_QUOT_BITS_PER_CYCLE-1:0] quot_bit_swap[PIPE_STAGE_CNT-1:0];
logic [D_QUOT_BITS_PER_CYCLE-1:0] quot_bit_swap_i[PIPE_STAGE_CNT-1:0];

genvar i;
generate 
    for(i = 0; i < PIPE_STAGE_CNT; i++) begin
        assign quot_bit_swap[i] = quot_bit[D_QUOT_BITS_PER_CYCLE*i +: D_QUOT_BITS_PER_CYCLE];
        assign quot_bit_swap_i[i] = {<<{quot_bit_swap[i]}};

        del_chain 
        #(
            .IN_WORD_WDT(D_QUOT_BITS_PER_CYCLE),
            .DEL_CYC_LEN(PIPE_STAGE_CNT - i)
        )
        quot_bits_triang_del_chain
        (
            .clk(clk),
            .rst_n(rst_n),
            .clk_en(clk_en),
            .in_word(quot_bit_swap_i[i]),
            .in_word_val(),
            .in_word_del(res_quot[D_QUOT_WORD_WDT-1 - i*D_QUOT_BITS_PER_CYCLE -: D_QUOT_BITS_PER_CYCLE]),
            .in_word_val_del()
        );
    end
endgenerate

del_chain 
#(
    .IN_WORD_WDT(1),
    .DEL_CYC_LEN(PIPE_STAGE_CNT + 1)
)
res_val_del_chain
(
    .clk(clk),
    .rst_n(rst_n),
    .clk_en(clk_en),
    .in_word(op_val),
    .in_word_val(),
    .in_word_del(res_val),
    .in_word_val_del()
);

//synthesis translate_off
property asrt_int_div_res;
int d_end_sa;
int d_or_sa;
@(posedge clk) (clk_en & op_val, d_end_sa = op_d_end, d_or_sa = op_d_or) |-> ##[(PIPE_STAGE_CNT+1):100] (res_val & (res_quot == d_end_sa/d_or_sa) & (res_rem == d_end_sa % d_or_sa) );
endproperty

assert property (asrt_int_div_res) else $error("Incorrect quotient %d and remainder %d!", res_quot, res_rem);

asrt_int_div_quot_range: assert property (@(posedge clk) disable iff (!rst_n) (clk_en & op_val |-> op_d_end/op_d_or < 2**D_QUOT_WORD_WDT)) 
    else $error("The dividend %d and divisor %d will result in quotient overflow!", op_d_end, op_d_or);

asrt_int_div_rem_range: assert property (@(posedge clk) disable iff (!rst_n) (clk_en & op_val |-> op_d_end % op_d_or < 2**D_QUOT_WORD_WDT)) 
    else $error("The dividend %d and divisor %d will result in remainder overflow!", op_d_end, op_d_or);

asrt_int_div_d_or_range: assert property (@(posedge clk) disable iff (!rst_n) (clk_en & op_val |-> op_d_or < 2**(D_OR_WORD_WDT-1))) 
    else $error("The divisor %d is too large and cannot be represented as 2s complement!", op_d_or);

asrt_int_div_by_zero: assert property (@(posedge clk) disable iff (!rst_n) (clk_en & op_val |-> op_d_or != 0)) 
    else $error("The divisor shall not be zero!");

initial begin
    assert(DIV_STAGE_CNT % D_QUOT_BITS_PER_CYCLE == 0) else $fatal(1, "Bits per cycle shall divide number of quotient bits!");
end

//synthesis translate_on

endmodule