`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     lead_zero_cnt
// Project Name:    Efficient FPGA CNN implementation
// Description:     leading zero counter, recursive tree structure, only combinational logic
// Synthesizable:   Yes
///////////////////////////////////////////////////////////////////////////////////////////////


module lead_zero_cnt
#(
    parameter IN_WORD_WDT = 64,
    parameter OUT_WORD_WDT = $clog2(IN_WORD_WDT*4) 
) 
(
    input logic  [IN_WORD_WDT-1:0] in_word_lhs,
    input logic  [IN_WORD_WDT-1:0] in_word_rhs,
    output logic [OUT_WORD_WDT-1:0] out_word
);

  logic [OUT_WORD_WDT-2:0] leading_zero_rhs;
  logic [OUT_WORD_WDT-2:0] leading_zero_lhs;

  generate
    if(IN_WORD_WDT == 1) begin : triv
      always_comb begin
        casez({in_word_lhs, in_word_rhs})
            2'b00   : out_word = 2'b10; //2 leading zeros
            2'b01   : out_word = 2'b01; //1 leading zeros
            2'b1?   : out_word = 2'b00; //no leading zeros
            default : out_word = 2'b00; //no leading zeros;
        endcase
      end
    end else if (IN_WORD_WDT == 2) begin : leaf
        //encode pairs of bits
      always_comb begin
        casez(in_word_lhs)
            2'b00   : leading_zero_lhs = 2'b10; //2 leading zeros
            2'b01   : leading_zero_lhs = 2'b01; //1 leading zeros
            2'b1?   : leading_zero_lhs = 2'b00; //no leading zeros
            default : leading_zero_lhs = 2'b00; //no leading zeros;
        endcase
        
        casez(in_word_rhs)
            2'b00   : leading_zero_rhs = 2'b10; //2 leading zeros
            2'b01   : leading_zero_rhs = 2'b01; //1 leading zeros
            2'b1?   : leading_zero_rhs = 2'b00; //no leading zeros
            default : leading_zero_rhs = 2'b00; //no leading zeros;
        endcase
      end
    end else begin : node   
        //left tree
        lead_zero_cnt 
        #(
            .IN_WORD_WDT (IN_WORD_WDT/2)
        ) 
        lhs_tree
        (
            .in_word_lhs  (in_word_lhs[IN_WORD_WDT-1 -: IN_WORD_WDT/2]),
            .in_word_rhs  (in_word_lhs[IN_WORD_WDT/2-1 -: IN_WORD_WDT/2]),
            .out_word (leading_zero_lhs)
        );
       
        //right tree
        lead_zero_cnt 
        #(
            .IN_WORD_WDT (IN_WORD_WDT/2)
        ) 
        rhs_tree
        (
            .in_word_lhs  (in_word_rhs[IN_WORD_WDT-1 -: IN_WORD_WDT/2]),
            .in_word_rhs  (in_word_rhs[IN_WORD_WDT/2-1 -: IN_WORD_WDT/2]),
            .out_word (leading_zero_rhs)
        );

    end
  endgenerate

  generate 
    if(IN_WORD_WDT > 1) begin
      always_comb begin : merge_block
        //merge
        if(leading_zero_lhs == 2**(OUT_WORD_WDT-2) & leading_zero_rhs == 2**(OUT_WORD_WDT-2)) //if left and right node = 10..0, then merge to 10..00
          out_word = {leading_zero_lhs, 1'b0};
        else if(leading_zero_lhs[OUT_WORD_WDT-2] == 1'b0) //if left node MSB is 0, merge to left node
          out_word = {1'b0, leading_zero_lhs};
        else //left node MSB is 1, merge to addition
          out_word = {2'b01, leading_zero_rhs[OUT_WORD_WDT-3:0]};
      end
    end
  endgenerate

endmodule
