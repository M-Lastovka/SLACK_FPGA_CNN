
"""
Author: Martin Lastovka, @RWTH DSP 
Project: Efficient FPGA CNN implementation for 5G physical layer - Master Thesis @ RWTH DSP
Desc: TODO, TODO: split into two scripts
"""

import numpy as np
from fxpmath import Fxp as fxp
import matplotlib.pyplot as plt
import cnn_params as cnn_p
import gen_tanh_lut as tanh_lut
import csv

def comp_conv_dims(tens_in_dim, kern_size, stride, padding):
    tens_dim_0 = int(np.floor((tens_in_dim[0] + 2*padding[0] - kern_size[0]) / stride[0] + 1))
    tens_dim_1 = int(np.floor((tens_in_dim[1] + 2*padding[1] - kern_size[1]) / stride[1] + 1))
    return tens_dim_0, tens_dim_1

def tens_set_stream_padding(tens_data, tens_layout, stream_padding): #set the padding values to zero
    if(len(tens_data.shape) == 2):
        if(tens_layout == cnn_p.layout_t.COL_FIRST):
            tens_data[-1:-1-stream_padding:-1, :] = 0
        else:
            tens_data[:, -1:-1-stream_padding:-1] = 0
    elif(len(tens_data.shape) == 3):
        tens_data[:, :, -1:-1-stream_padding:-1] = 0
    else:
        tens_data[:, :, -1:-1-stream_padding:-1, :] = 0

def load_tens_data(tens, h2c_data_source, stream_padding): #load the data for the H2C transfer, either generate it here or load from a file
    tot_lmnt = 1
    for dim in tens.dims:
        tot_lmnt = dim * tot_lmnt
    match h2c_data_source:
        case "rand_gauss":
            np.random.seed(0)
            tens_real = np.random.normal(loc=0, scale=0.1, size=tens.dims)
        case "lin_index":
            lin_index  = np.arange(tot_lmnt)
            tens_real = lin_index.reshape(tens.dims)
        case _: #source is in a file
            #separate into file name and key
            split_str = h2c_data_source.split('\\')
            file_name = split_str[0]
            data_key  = split_str[1]
            assert file_name.endswith('.csv'), "Error, only supported H2C data source file extension is .csv"
            #read the file
            data_dict = {}
            with open(file_name, 'r') as file:
                reader = csv.reader(file)
                for row in reader:
                    key = row[0]
                    values = list(map(float, row[1:]))
                    data_dict[key] = values

            if data_key in data_dict:
                tens_real_flat = np.array(data_dict[data_key])
                #get the original shape
                orig_shape = None
                if(len(tens.dims) == 2):
                    if(tens.layout == cnn_p.layout_t.COL_FIRST):
                        orig_shape = (tens.dims[0] - stream_padding, tens.dims[1])
                        padd_width = ((0, int(np.ceil(orig_shape[0] / cnn_p.C_VECT_SIZE) * cnn_p.C_VECT_SIZE) - orig_shape[0]), (0, 0))                        
                    else:
                        orig_shape = (tens.dims[0], tens.dims[1] - stream_padding) 
                        padd_width = ((0, 0), (0, int(np.ceil(orig_shape[1] / cnn_p.C_VECT_SIZE) * cnn_p.C_VECT_SIZE) - orig_shape[1])) 
                elif(len(tens.dims) == 3):
                    orig_shape = (tens.dims[0], tens.dims[1], tens.dims[2] - stream_padding)
                    padd_width = ((0, 0), (0, 0), (0, int(np.ceil(orig_shape[2] / cnn_p.C_VECT_SIZE) * cnn_p.C_VECT_SIZE) - orig_shape[2])) 
                else:
                    orig_shape = (tens.dims[0], tens.dims[1], tens.dims[2] - stream_padding, tens.dims[3])
                    padd_width = ((0, 0), (0, 0), (0, int(np.ceil(orig_shape[2] / cnn_p.C_VECT_SIZE) * cnn_p.C_VECT_SIZE) - orig_shape[2]), (0, 0)) 

                tens_data       = tens_real_flat.reshape(orig_shape) #reshape
                tens_real       = np.pad(tens_data, padd_width, mode='constant') #add padding to align dims
            else:
                print(f"Key '{data_key}' not found in the CSV file.")

    #apply padding (set padding values to zero) and convert to fixed-point            
    tens_set_stream_padding(tens_real, tens.layout, stream_padding)

    tens_fxp  = fxp(np.float32(tens_real)).like(cnn_p.FXP_EXT_WORD)

    return tens_fxp, tens_real

def plot_hist(x, eq_bins=20, title="histogram"):
    hist, bins = np.histogram(x, bins=eq_bins)
    hist = hist / hist.sum()
    bin_centers = (bins[:-1] + bins[1:]) / 2
    plt.bar(bin_centers, hist, width=(bins[1] - bins[0]), edgecolor='k', alpha=0.7)
    plt.xlabel('Value')
    plt.ylabel('Probability')
    plt.title(title)
    plt.show()

def padd_mat_vect(mat, dim2padd, vect_wdt):
    return np.pad(mat, ((0, dim2padd[0]*int(np.ceil(mat.shape[0] / vect_wdt) * vect_wdt - mat.shape[0])), (0, dim2padd[1]*int(np.ceil(mat.shape[1] / vect_wdt) * vect_wdt - mat.shape[1]))), mode='constant')

def init_tens3d_lin_index(h, w, c):

    #create meshgrid for each dimension
    meshgrid_h, meshgrid_w, meshgrid_c = np.meshgrid(np.arange(h), np.arange(w), np.arange(c), indexing='ij')
    
    #calculate linear index for each entry
    tens = 1 + meshgrid_w + meshgrid_h * w + meshgrid_c * (w * h)
    
    return tens

def init_tens4d_lin_index(h, w, c, l):
    #create meshgrid for each dimension
    meshgrid_h, meshgrid_w, meshgrid_c, meshgrid_l = np.meshgrid(np.arange(h), np.arange(w), np.arange(c), np.arange(l), indexing='ij')
    
    #calculate linear index for each entry
    tens = 1 + meshgrid_w + meshgrid_h * w + meshgrid_c * (w * h) + meshgrid_l * (w * h * c)
    
    return tens

def conv_sum3d(x, y, fxp_mode = False):
    dim_x = x.shape
    dim_y = y.shape
    assert dim_x == dim_y, "The dimensions of the tensors have match!"

    if(fxp_mode):
        p_sum = fxp(0.0).like(cnn_p.FXP_INT_WORD)
    else:
        p_sum = 0.0
    
    for i in range(dim_x[0]):
        for j in range(dim_x[1]):
            for k in range(dim_x[2]):
                p_sum = p_sum + x[i,j,k]*y[i,j,k]

    return p_sum

def tens_trans_bias(mtx, bias, fxp_mode=False):
    if(bias.shape[1] == 1): #replicated bias
        if(fxp_mode):
            repl_bias = fxp(np.zeros((bias.shape[0], mtx.shape[1]))).like(cnn_p.FXP_INT_WORD)
            for i in range(mtx.shape[1]):
                for j in range(bias.shape[0]):
                    repl_bias[j, i] = bias[j]
        else:
            repl_bias = np.tile(bias, mtx.shape[1])
        return mtx + repl_bias
    else:
        return mtx + bias

def tens_trans_batch(tens, batch_norm, fxp_mode=False):
    if(len(tens.shape) == 2):
        if(fxp_mode):
            scale  = fxp(np.zeros(tens.shape)).like(cnn_p.FXP_INT_WORD)
            shift  = fxp(np.zeros(tens.shape)).like(cnn_p.FXP_INT_WORD)
            for i in range(tens.shape[1]):
                for j in range(tens.shape[0]):
                    scale[j, i] = batch_norm[j, 0]
                    shift[j, i] = batch_norm[j, 1]
        else:
            scale = np.tile(batch_norm[:, 0][:, np.newaxis], tens.shape[1])
            shift = np.tile(batch_norm[:, 1][:, np.newaxis], tens.shape[1])
    else:
        if(fxp_mode):
            scale  = fxp(np.zeros(tens.shape)).like(cnn_p.FXP_INT_WORD)
            shift  = fxp(np.zeros(tens.shape)).like(cnn_p.FXP_INT_WORD)
            for i in range(tens.shape[0]):
                for j in range(tens.shape[1]):
                    for k in range(tens.shape[2]):
                        scale[i, j, k] = batch_norm[k, 0]
                        shift[i, j, k] = batch_norm[k, 1]
        else:
            i, j, k = tens.shape
            batch_norm_temp = batch_norm[:, 0].reshape(k, 1, 1)
            scale = np.tile(batch_norm_temp, (1, i, j)).transpose(1, 2, 0)
            batch_norm_temp = batch_norm[:, 1].reshape(k, 1, 1)
            shift = np.tile(batch_norm_temp, (1, i, j)).transpose(1, 2, 0)
    return tens * scale + shift

def tens_trans_lin(src_a, src_b, tens_trans_spec, batch_norm, bias, fxp_mode=False): #compute the linear transformation
    if(fxp_mode):
        src_a_data      = src_a.data_accel
        src_b_data      = src_b.data_accel
        bias_data       = bias.data_accel
        batch_norm_data = batch_norm.data_accel
    else:
        src_a_data      = src_a.data_real
        src_b_data      = src_b.data_real
        bias_data       = bias.data_real
        batch_norm_data = batch_norm.data_real
    mtx_prod = matmul(src_a_data, src_b_data, fxp_mode)
    if(tens_trans_spec.bias_en):
        mtx_prod = tens_trans_bias(mtx_prod, bias_data, fxp_mode)
    if(tens_trans_spec.batch_norm_en):
        mtx_prod = tens_trans_batch(mtx_prod, batch_norm_data, fxp_mode)

    res = nlin_f(mtx_prod, tens_trans_spec.nlin_f_type, fxp_mode)
    return res

def tens_trans_conv(src_a, src_b, tens_trans_spec, batch_norm, bias, fxp_mode=False): #compute the linear transformation
    if(fxp_mode):
        src_a_data      = src_a.data_accel
        src_b_data      = src_b.data_accel
        bias_data       = bias.data_accel
        batch_norm_data = batch_norm.data_accel
    else:
        src_a_data      = src_a.data_real
        src_b_data      = src_b.data_real
        bias_data       = bias.data_real
        batch_norm_data = batch_norm.data_real
    conv_map = conv3d(src_b_data, src_a_data, bias_data, (tens_trans_spec.conv_cfg.conv_stride_0, tens_trans_spec.conv_cfg.conv_stride_1), (tens_trans_spec.conv_cfg.conv_padding_0, tens_trans_spec.conv_cfg.conv_padding_1), fxp_mode)
    if(not fxp_mode): #for reference when debugging
        conv_map_test = conv3d_sys_arr(src_b_data, src_a_data, bias_data, (tens_trans_spec.conv_cfg.conv_stride_0, tens_trans_spec.conv_cfg.conv_stride_1), (tens_trans_spec.conv_cfg.conv_padding_0, tens_trans_spec.conv_cfg.conv_padding_1), fxp_mode)
    if(tens_trans_spec.batch_norm_en):
        conv_map = tens_trans_batch(conv_map, batch_norm_data, fxp_mode)

    res = nlin_f(conv_map, tens_trans_spec.nlin_f_type, fxp_mode)
    return res

def nlin_f(tens_in_data, nlin_f_type, fxp_mode=False): #compute non-linear function
    match nlin_f_type:
        case cnn_p.nlin_f_type_t.NLIN_F_IDENTITY:
            res = tens_in_data
        case cnn_p.nlin_f_type_t.NLIN_F_RELU:
            res = tens_in_data * (tens_in_data > 0)
        case cnn_p.nlin_f_type_t.NLIN_F_TANH:
            if(fxp_mode):
                tens_in_data_np_flat = tens_in_data.real.flatten()
                for i, x in enumerate(tens_in_data_np_flat):
                    tens_in_data_np_flat[i] = tanh_lut.comp_tanh_hybrid(tanh_arg=x, tanh_lut=cnn_p.C_TANH_LUT_MEM)
                tens_in_data_np = tens_in_data_np_flat.reshape(tens_in_data.shape)
                res = fxp(tens_in_data_np).like(cnn_p.FXP_INT_WORD)
            else:
                res = np.tanh(tens_in_data)
        case _:
            assert False, "Error, not yet implemented"
    return res


def maxpool_3d(tens_in_data, kern_size, stride, padding, padding_value):

    padd_width          = ((padding[0], padding[0]), (padding[1], padding[1]), (0, 0))
    tens_in_data_padd = np.pad(tens_in_data, padd_width, mode='constant', constant_values=padding_value)

    tens_out_dim_0, tens_out_dim_1 = comp_conv_dims(tens_in_data.shape, kern_size, stride, padding)
    tens_out_dim = (tens_out_dim_0, tens_out_dim_1, tens_in_data.shape[2])

    tens_out_data = np.zeros(tens_out_dim)

    for y in range(0, tens_out_dim[0]):
        for x in range(0, tens_out_dim[1]):
                wind  = tens_in_data_padd[y * stride[0] : y * stride[0] + kern_size[0], x * stride[1] : x * stride[1] + kern_size[1], :]
                max_wind = np.max(wind, axis=(0,1))
                tens_out_data[y, x, :] = max_wind

    return tens_out_data

def tens_trans_maxpool(src, tens_trans_spec, fxp_mode=False):
    
    if(fxp_mode):
        src_data = src.data_accel
    else:
        src_data = src.data_real
    maxpool_res = maxpool_3d(src_data, kern_size=(((tens_trans_spec.tens_trans_dims.tens_src_a_dims.tens_0_dim, tens_trans_spec.tens_trans_dims.tens_src_a_dims.tens_1_dim))), stride=((tens_trans_spec.conv_cfg.conv_stride_0, tens_trans_spec.conv_cfg.conv_stride_1)), padding=(((tens_trans_spec.conv_cfg.conv_padding_0, tens_trans_spec.conv_cfg.conv_padding_1))), padding_value=-2**(cnn_p.C_ARITH_FXP_INT_WDT-1))
    if(fxp_mode):
        res = fxp(maxpool_res).like(cnn_p.FXP_EXT_WORD)
    else:
        res = maxpool_res
    return res

def conv3d(tens_in_data, kern_data, bias_data=None, stride = (0, 0), padding = (0, 0), fxp_mode=False):
    #dimensions
    tens_dim_in     = tens_in_data.shape
    kern_dim        = kern_data.shape
    tens_out_dim    = (((tens_dim_in[0]+2*padding[0]-kern_dim[0])//stride[0]) + 1, ((tens_dim_in[1]+2*padding[1]-kern_dim[1])//stride[1]) + 1, kern_dim[3])

    #padding
    padd_width          = ((padding[0], padding[0]), (padding[1], padding[1]), (0, 0))
    tens_in_data_padd   = np.pad(tens_in_data, padd_width, mode='constant')

    #initialize output tensor
    if(fxp_mode):
        tens_out_data = fxp(np.zeros(tens_out_dim)).like(cnn_p.FXP_INT_WORD)
    else:
        tens_out_data = np.zeros(tens_out_dim)

    #convolution
    for y in range(0, tens_out_dim[0]):
        print(f"DEBUG: y: {y}")
        for x in range(0, tens_out_dim[1]):
            for z in range(0, tens_out_dim[2]):
                conv_sum = conv_sum3d(tens_in_data_padd[y * stride[0] : y * stride[0] + kern_dim[0], x * stride[1] : x * stride[1] + kern_dim[1], :], kern_data[:, :, :, z], fxp_mode)
                if bias_data is not None:
                    tens_out_data[y, x, z] = conv_sum + bias_data[z]
                else:
                    tens_out_data[y, x, z] = conv_sum

    return tens_out_data

def matmul(x, y, fxp_mode = False):
    if(len(y.shape) == 2):
        y_flat = y
    elif(len(y.shape) == 3):
        y_flat = []
        if(fxp_mode):
            y_np = y.real
        else:
            y_np = y
        for i in range(y_np.shape[2] // cnn_p.C_VECT_SIZE):
            y_flat.append(y_np[:, :, i * cnn_p.C_VECT_SIZE : (i + 1) * cnn_p.C_VECT_SIZE].ravel())
        y_flat = np.concatenate(y_flat)
        y_flat = y_flat.reshape((-1, 1))
    else:
        y_flat = []
        if(fxp_mode):
            y_np = y.real
        else:
            y_np = y
        for j in range(y_np.shape[3]):
            for i in range(y_np.shape[2] // cnn_p.C_VECT_SIZE):
                y_flat.append(y_np[:, :, i * cnn_p.C_VECT_SIZE : (i + 1) * cnn_p.C_VECT_SIZE, j].ravel())
        y_flat = np.concatenate(y_flat)
        y_flat = y_flat.reshape((-1, y_np.shape[3]))
    assert x.shape[1] == y_flat.shape[0], "Error, non-matching dimensions for matrix multiplication"
    if(fxp_mode):
        y_flat = fxp(y_flat).like(cnn_p.FXP_INT_WORD)
        result = fxp(np.zeros((x.shape[0], y_flat.shape[1]))).like(cnn_p.FXP_INT_WORD)
        for i in range(x.shape[0]):      
            for j in range(y_flat.shape[1]):   
                for k in range(x.shape[1]):   
                    result[i, j] += x[i, k] * y_flat[k, j]
    else:
        result = np.matmul(x,y_flat)
    return result

def gen_conv_eq_mat(tens_in_data, kern_data, bias_data, stride = (0, 0), padding = (0, 0)):
    #dimensions
    tens_dim_in     = tens_in_data.shape
    kern_dim        = kern_data.shape
    tens_out_dim_0, tens_out_dim_1 = comp_conv_dims(tens_dim_in, kern_dim, stride, padding)
    tens_out_dim    = (tens_out_dim_0, tens_out_dim_1, kern_dim[3])

    #matrices dimensions
    kern_eq_mat_dim     = (kern_dim[3], kern_dim[0]*kern_dim[1]*kern_dim[2])
    tens_in_eq_mat_dim  = (kern_eq_mat_dim[1], tens_out_dim[0]*tens_out_dim[1])
    bias_eq_mat_dim     = (kern_eq_mat_dim[0], tens_in_eq_mat_dim[1])

    #initialize
    kern_eq_mat         = np.zeros(kern_eq_mat_dim)
    tens_in_eq_mat      = np.zeros(tens_in_eq_mat_dim)
    tens_in_eq_mat_i    = np.zeros(tens_in_eq_mat_dim)
    bias_eq_mat         = np.zeros(bias_eq_mat_dim)

    #padding
    padd_width          = ((padding[0], padding[0]), (padding[1], padding[1]), (0, 0))
    tens_in_data_padd   = np.pad(tens_in_data, padd_width, mode='constant')

    #generate equivalent kernel matrix
    for x in range(0, kern_eq_mat_dim[0]):
        kern_eq_mat[x, :] = kern_data[:, :, :, x].transpose((0, 1, 2)).reshape(-1)

    #generate equivalent tensor input matrix
    for z in range(0, tens_in_eq_mat_dim[1]):
        y = (z // tens_out_dim[1])*stride[0]
        x = (z % tens_out_dim[1])*stride[1]
        tens_in_eq_mat[:, z] = tens_in_data_padd[y:y+kern_dim[0], x:x+kern_dim[1], :].transpose((0, 1, 2)).reshape(-1)

    #generate equivalent tensor input matrix by indexing
    vect_ch_fact = tens_dim_in[2] // cnn_p.C_VECT_SIZE
    for i in range(0, tens_in_eq_mat_dim[0] // cnn_p.C_VECT_SIZE):
        for j in range(0, tens_in_eq_mat_dim[1]):
            x = (j * stride[1] % (tens_out_dim[1] * stride[1])) + ((i // vect_ch_fact) % kern_dim[1])
            y = (j * stride[1] // (tens_out_dim[1] * stride[1])) * stride[0] + ((i // vect_ch_fact) // kern_dim[1])
            z = i % vect_ch_fact
            x_off = x - padding[1]
            y_off = y - padding[0]
            z_off = z
            addr = x_off + tens_dim_in[1] * (y_off +  tens_dim_in[0] * z_off)
            padding_vect = (x_off < 0 or x_off > tens_dim_in[1] - 1 or y_off < 0 or y_off > tens_dim_in[0] - 1)
            print(f"x: {x}, y: {y}, z: {z}, addr: {addr}, padd: {padding_vect}, i: {i}, j: {j}")
            if(padding_vect): 
                tens_in_eq_mat_i[i * cnn_p.C_VECT_SIZE : (i + 1) * cnn_p.C_VECT_SIZE, j] = np.zeros(cnn_p.C_VECT_SIZE)
            else:
                tens_in_eq_mat_i[i * cnn_p.C_VECT_SIZE : (i + 1) * cnn_p.C_VECT_SIZE, j] = tens_in_data[y_off, x_off, z_off * cnn_p.C_VECT_SIZE : (z_off + 1) * cnn_p.C_VECT_SIZE]

    diff = tens_in_eq_mat_i - tens_in_eq_mat
    if(np.array_equal(diff, np.zeros(diff.shape))):
        print("The equivalent matrices match!")
    else:
        print("The equivalent matrices do not match!")
    
    #generate equivalent bias matrix
    for x in range(0, bias_eq_mat_dim[0]):
        bias_eq_mat[x, :] = np.repeat(bias_data[x], bias_eq_mat_dim[1])

    return kern_eq_mat, tens_in_eq_mat, bias_eq_mat

def block_matmul(src_a, src_b, bias):
    if(bias.shape[1] == 1):
        bias_mod = np.tile(bias, src_b.shape[1])
    else:
        bias_mod = bias
    res = np.zeros((src_a.shape[0], src_b.shape[1]))
    #block matrix multiplication
    for i in range(0, src_a.shape[0] // cnn_p.C_VECT_SIZE):
        acc = bias_mod[i*cnn_p.C_VECT_SIZE:(i+1)*cnn_p.C_VECT_SIZE, :]
        for j in range(0, src_a.shape[1]//cnn_p.C_VECT_SIZE):
            src_a_block = src_a[i*cnn_p.C_VECT_SIZE:(i+1)*cnn_p.C_VECT_SIZE, j*cnn_p.C_VECT_SIZE:(j+1)*cnn_p.C_VECT_SIZE]
            src_b_block = src_b[j*cnn_p.C_VECT_SIZE:(j+1)*cnn_p.C_VECT_SIZE, :]
            bmm = np.matmul(src_a_block, src_b_block)
            acc = bmm + acc
        res[i*cnn_p.C_VECT_SIZE:(i+1)*cnn_p.C_VECT_SIZE, :] = acc
    return res


def conv3d_sys_arr(src_a, src_b, bias, stride, padding, fxp_mode=False):
    #get equivalent matrices
    src_a_eq_mat, src_b_eq_mat, bias_eq_mat = gen_conv_eq_mat(src_a, src_b, bias, stride, padding)
    res = block_matmul(src_a_eq_mat, src_b_eq_mat, bias_eq_mat) #TODO: fxp mode
    return res

def fxp_mse_compar_test(tens_dim_in, kern_dim, padding, stride, bias_dim, layer_cnt): #compute MSE of a fixed-point model with a reference solution, TODO: specify network and test with YAML, now just a single conv layer 
    
    #initialize the reference values as uniform gaussian
    tens_in_data    = np.random.normal(loc=0, scale=1, size=tens_dim_in)
    kern_data       = np.random.normal(loc=0, scale=1, size=kern_dim)
    bias_data       = np.random.normal(loc=0, scale=1, size=bias_dim)

    #initialize the fixed point values by casting the reference
    tens_in_data_fxp = fxp(tens_in_data).like(cnn_p.FXP_INT_WORD)
    kern_data_fxp    = fxp(kern_data).like(cnn_p.FXP_INT_WORD)
    bias_data        = fxp(bias_data).like(cnn_p.FXP_INT_WORD)

    fxp_mse = np.zeros(layer_cnt)

    #compute
    for i in range(layer_cnt):
        tens_out_data_ref = conv3d(tens_in_data, kern_data, bias_data, stride, padding, fxp_mode=False) #reference
        tens_out_data_fxp = conv3d(tens_in_data_fxp, kern_data_fxp, bias_data, stride, padding, fxp_mode=True) #fixed point

        #calculate MSE and NMSE
        tens_out_diff = tens_out_data_ref - tens_out_data_fxp.real
        fxp_mse[i] = np.mean(tens_out_diff**2)

        tens_in_data      = tens_out_data_ref
        tens_in_data_fxp  = tens_out_data_fxp

    #plot results
    plt.plot(fxp_mse)
    plt.xlabel('Layer index [-]')
    plt.ylabel('MSE [-]')
    plt.title('MSE of conv3d layer')
    plt.show()

def fxp_fused_bnorm_compar(weight_dim, batch_size): 
    
    #initialize the reference values as uniform gaussian
    weight    = np.random.normal(loc=0, scale=1, size=weight_dim) + np.random.uniform(-0.95, 1.12, size=weight_dim)
    data      = np.random.normal(loc=0, scale=1, size=(weight_dim[1], batch_size))
    bias      = np.random.normal(loc=0, scale=1, size=(weight_dim[0], 1)) + np.random.uniform(-0.95, 1.12, size=(weight_dim[0], 1))
    bias      = np.tile(bias, batch_size)

    #compute output
    res = np.matmul(weight, data) + bias
    #compute mean and std per row
    means = np.mean(res, axis=1)
    stds  = np.std(res, axis=1) + 0.0001
    norm_stds = np.reciprocal(stds)
    scale = np.tile(norm_stds[:, np.newaxis], batch_size)
    offset = -1*np.tile(means[:, np.newaxis], batch_size)*scale

    res_true = res*scale + offset
    mu = np.mean(res_true, axis=1)
    std = np.std(res_true, axis=1)

    #initialize the fixed point values by casting the reference
    weight_fxp      = fxp(weight).like(cnn_p.FXP_INT_WORD)
    data_fxp        = fxp(data).like(cnn_p.FXP_INT_WORD)
    bias_fxp        = fxp(bias).like(cnn_p.FXP_INT_WORD)
    scale_fxp       = fxp(scale).like(cnn_p.FXP_INT_WORD)
    offset_fxp      = fxp(offset).like(cnn_p.FXP_INT_WORD)   

    res_fxp_nfuse = (matmul(weight_fxp, data_fxp, True) + bias_fxp)*scale_fxp + offset_fxp
    mse_fxp_nfuse = np.mean((res_true - res_fxp_nfuse.real)**2)
    
    weight_fxp_fuse = weight_fxp*np.tile((scale_fxp[:, 0])[:, np.newaxis], weight_fxp.shape[1])
    bias_fxp_fuse = bias_fxp*scale_fxp + offset_fxp

    res_fxp_fuse = matmul(weight_fxp_fuse, data_fxp) + bias_fxp_fuse
    mse_fxp_fuse = np.mean((res_true - res_fxp_fuse.real)**2)

    print("MSE fused: " + str(mse_fxp_fuse) + " MSE non-fused: " + str(mse_fxp_nfuse))

def verify_eq_conv(tens_dim_in, kern_dim, padding, stride, bias_dim, vect_wdt): #verify the equivalent matrix approach for conv layer

    #generate some easily verifiable data
    tens_in_data    = init_tens3d_lin_index(tens_dim_in[0], tens_dim_in[1], tens_dim_in[2])
    kern_data       = init_tens4d_lin_index(kern_dim[0], kern_dim[1], kern_dim[2], kern_dim[3])
    bias_data       = np.array(np.arange(bias_dim))

    #reference solution
    tens_out_data_ref = conv3d(tens_in_data, kern_data, bias_data, stride, padding)

    #get equivalent matrices
    kern_eq_mat, tens_in_eq_mat, bias_eq_mat = gen_conv_eq_mat(tens_in_data, kern_data, bias_data, stride, padding)

    #compute the result by matrix multiplication
    tens_out_eq_mat = np.matmul(kern_eq_mat, tens_in_eq_mat) + bias_eq_mat

    #reshape into a tensor again
    tens_out_dim_0, tens_out_dim_1 = comp_conv_dims(tens_dim_in, kern_dim, stride, padding)
    tens_out_dim    = (tens_out_dim_0, tens_out_dim_1, kern_dim[3])
    tens_out_eq_data = np.zeros(tens_out_dim)

    for i in range(0, tens_out_eq_mat.shape[1]):
        tens_out_eq_data[i // tens_out_eq_data.shape[1], i % tens_out_eq_data.shape[1], :] = tens_out_eq_mat[:, i]
    
    diff = tens_out_eq_data - tens_out_data_ref
    if(np.array_equal(diff, np.zeros(diff.shape))):
        print("The tensors match!")
    else:
        print("The tensors do not match!")


def main():
    np.random.seed(999)

    #fxp_fused_bnorm_compar((20, 20), 10)

    # setup all parameters and data dimensions
    tens_ch_in      = 5
    tens_ch_out     = 10
    tens_dim_in     = (7, 5, tens_ch_in)
    kern_dim        = (3, 3, tens_ch_in, tens_ch_out)
    padding       = (1, 1)
    stride     = (1, 1)
    bias_dim        = tens_ch_out
    vect_wdt        = 5

    #fxp_mse_compar_test(tens_dim_in, kern_dim, padding, stride, bias_dim, 4)
    verify_eq_conv(tens_dim_in, kern_dim, padding, stride, bias_dim, vect_wdt)



if __name__ == "__main__":
    main()