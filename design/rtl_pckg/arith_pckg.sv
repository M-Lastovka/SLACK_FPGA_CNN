`timescale 1ns / 1ps
///////////////////////////////////////////////////////////////////////////////////////////////
// Institution:     RWTH Aachen - DSP chair
// Author:          Martin Lastovka : martin.lastovka@dsp.rwth-aachen.de
// Module Name:     arith_pckg
// Project Name:    Efficient FPGA CNN implementation
// Description:     package for the arithmetic blocks
// Synthesizable:   No
///////////////////////////////////////////////////////////////////////////////////////////////

package arith_pckg;

typedef enum 
{
    ADDR_OPT_FPGA, 
    FIXED_POINT_GENERIC,
    FIXED_POINT_OPT_FPGA, 
    FLOATING_POINT        //TODO reserved for future implementation
} arith_type_t;

typedef struct 
{
    int int_wdt;
    int frac_wdt;
} fxp_cfg_t;

typedef struct
{
    int word_wdt;
    fxp_cfg_t fxp_cfg;
    arith_type_t arith_type;
    bit arith_satur;

} arith_cfg_t;

//general configuration

parameter C_ARITH_WORD_LEN = 18;
parameter bit C_ADD_ARITH_SATUR = 1;
parameter bit C_MULT_ARITH_SATUR = C_ADD_ARITH_SATUR;
parameter arith_type_t C_ADD_ARITH_TYPE = FIXED_POINT_GENERIC;
parameter arith_type_t C_MULT_ARITH_TYPE = FIXED_POINT_OPT_FPGA;

//fixed point configuration

parameter C_ADD_FXP_IN_CYC_LEN = 1;
parameter C_ADD_FXP_OUT_CYC_LEN = 1;
parameter C_ADD_FXP_CYC_LEN = C_ADD_FXP_IN_CYC_LEN + C_ADD_FXP_OUT_CYC_LEN;
parameter C_MULT_FXP_IN_CYC_LEN = 3;
parameter C_MULT_FXP_OUT_CYC_LEN = 2;
parameter C_MULT_FXP_CYC_LEN = C_MULT_FXP_IN_CYC_LEN + C_MULT_FXP_OUT_CYC_LEN;
parameter C_ARITH_FXP_FRAC_WDT = 10;
parameter C_ARITH_FXP_INT_WDT = 8;

//global arithmetic configuration for adders and multipliers
parameter arith_cfg_t C_ADD_ARITH_CFG = '{word_wdt:C_ARITH_WORD_LEN, fxp_cfg:'{int_wdt:C_ARITH_FXP_INT_WDT, frac_wdt:C_ARITH_FXP_FRAC_WDT}, arith_type:C_ADD_ARITH_TYPE, arith_satur:C_ADD_ARITH_SATUR};
parameter arith_cfg_t C_MULT_ARITH_CFG = '{word_wdt:C_ARITH_WORD_LEN, fxp_cfg:'{int_wdt:C_ARITH_FXP_INT_WDT, frac_wdt:C_ARITH_FXP_FRAC_WDT}, arith_type:C_MULT_ARITH_TYPE, arith_satur:C_MULT_ARITH_SATUR};

parameter logic [C_ARITH_WORD_LEN-1:0] C_MIN_NEG_VALUE = {1'b1, {(C_ARITH_WORD_LEN-1){1'b0}}};
parameter logic [C_ARITH_WORD_LEN-1:0] C_MAX_POS_VALUE = {1'b0, {(C_ARITH_WORD_LEN-1){1'b1}}};

//get abs value of real
function automatic real abs_r(real input_val); 
    
    if(input_val < 0)
        return -input_val;
    else
        return input_val;

endfunction

//real to fixed point, with saturation, floor rounding
function automatic logic [C_ARITH_WORD_LEN-1:0] real2fxp(real input_val); 
    
    if(input_val > 2.0**(C_ARITH_FXP_INT_WDT-1) - 2.0**(-C_ARITH_FXP_FRAC_WDT))
        return C_MAX_POS_VALUE;
    else if(input_val < -2.0**(C_ARITH_FXP_INT_WDT-1))
        return C_MIN_NEG_VALUE;
    else
        return int'(input_val * 2.0**C_ARITH_FXP_FRAC_WDT);

endfunction

endpackage