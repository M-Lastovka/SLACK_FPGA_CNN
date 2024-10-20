
"""
Author: Martin Lastovka, @RWTH DSP 
Project: Efficient FPGA CNN implementation for 5G physical layer - Master Thesis @ RWTH DSP
Desc: Generate look-up table for tanh(x). Simple script which generates the LUT for tanh for signed fixed point arithmetic
#           characterized by integer bits count and fractional bits count. TODO: parameter description

"""

#!/usr/bin/env python3
import os
import cnn_params as cnn_p
import numpy as np
from fxpmath import Fxp as fxp
import matplotlib.pyplot as plt

def comp_tanh_hybrid(tanh_arg, tanh_lut):
    abs_tanh_arg = abs(tanh_arg)
    tanh_hybrid = 0
    if(abs_tanh_arg < cnn_p.C_TANH_LIN_END):
        tanh_hybrid = tanh_arg
    elif(abs_tanh_arg >= cnn_p.C_TANH_LIN_END and abs_tanh_arg <= cnn_p.C_TANH_SAT_START):
        lut_addr = int((abs_tanh_arg - cnn_p.C_TANH_LIN_END) // cnn_p.C_ARITH_FXP_ULP) // cnn_p.C_TANH_DOWN_SA_FACT
        tanh_hybrid = np.sign(tanh_arg) * tanh_lut[lut_addr].real
    else:
        tanh_hybrid = np.sign(tanh_arg) * 1.0
    return tanh_hybrid

def gen_tanh_lut():
    tanh_arg = cnn_p.C_TANH_LIN_END
    lut_addr = 0
    tanh_lut = []

    #generate the values and write to the file
    while not (tanh_arg > cnn_p.C_TANH_SAT_START and ((lut_addr - 1) & lut_addr == 0)):
        tanh_res     = np.tanh(tanh_arg)
        fxp_tanh_res = fxp(tanh_res).like(cnn_p.FXP_INT_WORD) 
        tanh_lut.append(fxp_tanh_res)
        lut_addr += 1
        tanh_arg += cnn_p.C_TANH_DOWN_SA_FACT*cnn_p.C_ARITH_FXP_ULP

    return tanh_lut


def write_tanh_lut_file(res_file_path='tanh_lut.txt', plot_lut=False): 
    # first, do some input checking
    assert isinstance(cnn_p.C_TANH_DOWN_SA_FACT, int) and cnn_p.C_TANH_DOWN_SA_FACT > 0 and cnn_p.C_TANH_DOWN_SA_FACT & (cnn_p.C_TANH_DOWN_SA_FACT-1) == 0, "Error: down sampling factor has to be positive integer and a power of two"
    assert isinstance(cnn_p.C_TANH_LIN_END, float) and cnn_p.C_TANH_LIN_END >= 0.0, "Error: End of linear phase has to be a positive float"
    assert isinstance(cnn_p.C_TANH_SAT_START, float) and cnn_p.C_TANH_SAT_START > 0.0, "Error: Start of saturation phase has to be a positive float"

    cnn_p.C_ARITH_FXP_ULP = 2.0**(-cnn_p.C_ARITH_FXP_FRAC_WDT)

    tanh_lut = gen_tanh_lut()

    #write to a file
    with open(os.path.join(os.getcwd(), res_file_path), 'w') as file:
        for x in tanh_lut:
            file.write(x.bin()[cnn_p.C_ARITH_FXP_INT_WDT:] + '\n')

    if(plot_lut):
        #compute and plot error
        #initialize
        x_ax_lim = 5
        sa_len = int((x_ax_lim - 0.0)//cnn_p.C_ARITH_FXP_ULP)
        tanh_hybrid = np.zeros(sa_len)
        tanh_ref = np.zeros(sa_len)
        tanh_mse_error = np.zeros(sa_len)

        for i in range(sa_len):
            tanh_arg = i*cnn_p.C_ARITH_FXP_ULP
            tanh_ref[i] = fxp(np.tanh(tanh_arg)).like(cnn_p.FXP_INT_WORD).real
            tanh_hybrid[i] = comp_tanh_hybrid(tanh_arg=tanh_arg, tanh_lut=tanh_lut)
            tanh_mse_error[i] = ((tanh_ref[i] - tanh_hybrid[i]))**2

        fig, (ax1, ax2) = plt.subplots(2, 1, sharex=True)

        #plot the LUT based hybrid implementation vs the reference 
        ax1.plot(tanh_ref, label='tanh ref', color='blue')
        ax1.plot(tanh_hybrid, label='tanh LUT', color='red')
        ax1.set_xlabel('x')
        ax1.set_ylabel('Tanh(x)')
        ax1.set_title('LUT implemenation plot')

        #plot the relative error
        ax2.plot(tanh_mse_error)
        ax2.set_xlabel('x')
        ax2.set_ylabel('relative error')
        ax2.set_title('Square error of implementations')

        plt.show()

        print("Tanh LUT generated, number of LUT entries: " + str(len(tanh_lut)) + ", size of LUT entry: " + str(cnn_p.C_ARITH_FXP_FRAC_WDT))
        print("MSE: " + str(np.mean(tanh_mse_error)) + ", std : " + str(np.std(tanh_mse_error)) + ", max : " + str(np.max(tanh_mse_error)))