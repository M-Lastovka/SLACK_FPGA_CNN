#!/usr/bin/python3
"""
Author: Martin Lastovka, @RWTH DSP 
Project: Efficient FPGA CNN implementation for 5G physical layer - Master Thesis @ RWTH DSP
Desc: Read descriptions of (possibly) multiple tensor transformation sequences, generate
      memory-mapped transactions for the simulation as a binary file and also generate the
      input data for the simulation, again as binary file
"""
#!/usr/bin/python3

import cnn_params as cnn_p
import cnn_regmap as cnn_r
import cnn_model as cnn_m
import gen_add_tree as add_tree
import gen_tanh_lut as tanh_lut
import yaml
import numpy as np
from fxpmath import Fxp as fxp
import argparse
import os
import random

def build(): #generate all the LUTs/RTL
    add_tree.gen_add_tree()
    tanh_lut.write_tanh_lut_file()
    cnn_p.C_TANH_LUT_MEM = tanh_lut.gen_tanh_lut()
    print("RTL build completed\n")

def eq_mtx_dim(dims, layout, norm=True, padding=0): #flatten 4D/3D/2D tensor to 2D, normalized by vector width where needed if norm is enabled
    if(norm):
        if(len(dims) == 2):
            return ((dims[0] - padding) // cnn_p.C_VECT_SIZE, dims[1]) if layout == cnn_p.layout_t.COL_FIRST else (dims[0], (dims[1] - padding) // cnn_p.C_VECT_SIZE)
        elif(len(dims) == 3):
            return ((dims[2] - padding) // cnn_p.C_VECT_SIZE, dims[0]*dims[1]) if layout == cnn_p.layout_t.COL_FIRST else (dims[2] - padding, dims[0]*dims[1]  // cnn_p.C_VECT_SIZE)
        elif(len(dims) == 4):
            return (dims[3] // cnn_p.C_VECT_SIZE, dims[0]*dims[1]*(dims[2] - padding)) if layout == cnn_p.layout_t.COL_FIRST else (dims[3], (dims[0]*dims[1]*(dims[2] - padding)) // cnn_p.C_VECT_SIZE)
        else:
            assert False, "Error, invalid number of input dimensions, shalle be in range <2,4>"
    else:
        if(len(dims) == 2):
            return (dims[0] - padding, dims[1]) if layout == cnn_p.layout_t.COL_FIRST else (dims[0], dims[1] - padding)
        elif(len(dims) == 3):
            return (dims[2] - padding, dims[0]*dims[1]) if layout == cnn_p.layout_t.COL_FIRST else (dims[2] - padding, dims[0]*dims[1])
        elif(len(dims) == 4):
            return (dims[3], dims[0]*dims[1]*(dims[2] - padding)) if layout == cnn_p.layout_t.COL_FIRST else (dims[3], dims[0]*dims[1]*(dims[2] - padding))
        else:
            assert False, "Error, invalid number of input dimensions, shalle be in range <2,4>"

def find_by_name(tens_set_search, name):
    tens_lst = [tens for tens in tens_set_search if tens.name in name]
    assert len(tens_lst) == 1, f"Error, could not find element {name} in the search set"
    return tens_lst[0]

def get_align_dim(tens_dims, tens_layout): 
    align_dim = None
    if(len(tens_dims) == 2):
        if(tens_layout == cnn_p.layout_t.COL_FIRST):
            align_dim = tens_dims[0]
        else:
            align_dim = tens_dims[1]
    elif(len(tens_dims) == 3 or len(tens_dims) == 4):
        align_dim = tens_dims[2]
    return align_dim

def gen_inter_repr(model_descr_file_path): #generate internal representation of the sequences

    with open(os.path.join(os.getcwd(), model_descr_file_path), 'r') as file:
        print("Producing internal representation based on file: " + os.path.join(os.getcwd(), model_descr_file_path) + "\n")
        tens_trans_seq_descr = yaml.safe_load(file)
        tens_trans_seq_lst = []
        for seq in tens_trans_seq_descr['tens_trans_seq']:
            tens_trans_seq = cnn_p.tens_trans_seq_t() #new sequence
            tens_trans_seq.name = seq['name']
            for trans in seq['tens_trans']:
                tens_trans = cnn_p.tens_trans_t() #new tensor transformation
                tens_trans.tens_trans_spec = cnn_p.tens_trans_spec_t()
                tens_gen = cnn_p.tens_t()
                tens_use = cnn_p.tens_t()
                if(len(tens_trans_seq.tens_trans_set) != 0):
                    tens_live_set_prev = tens_trans_seq.tens_trans_set[-1].tens_live_set #initialize live set to previous transformation in this sequence
                else:
                    if(seq['predecessor']):
                        tens_live_set_prev = find_by_name(tens_trans_seq_lst, seq['predecessor']).tens_trans_set[-1].tens_live_set #initialize live set to predecessor sequence
                    else:
                        tens_live_set_prev = None

                match trans['tens_trans_type']: #generate gen and use sets + specification (apart from addresses)
                    case 'TRANS_STREAM':
                        tens_trans.tens_trans_spec.tens_trans_type = cnn_p.tens_trans_type_t.TRANS_STREAM
                        assert 'res_name' in trans or 'src_name' in trans, "Error, stream shall be either h2c, c2h or duplex"
                        tens_src_a_dims = (0, 0)
                        tens_res_dims   = (0, 0)
                        if('res_name' in trans): #H2C stream
                            #extract gen set
                            tens_gen.dims = tuple(trans['res_dim']) 
                            tens_gen.layout = cnn_p.layout_t[trans['layout'].upper()]
                            tens_gen.name = trans['res_name']
                            tens_trans.tens_gen_set.append(tens_gen)

                            #set tensor operands name
                            tens_trans.res_name = trans['res_name']
                            tens_trans.h2c_data_source = trans['h2c_data_source']

                            #extract specification 
                            get_align_dim(tens_gen.dims, tens_gen.layout)
                            assert trans['res_stream_padding'] < cnn_p.C_VECT_SIZE, "Error, input padding shall not be larger or equal to the vector size"
                            assert trans['res_stream_padding'] > 0 and get_align_dim(tens_gen.dims, tens_gen.layout) == cnn_p.C_VECT_SIZE or trans['res_stream_padding'] == 0, "Error, if non-zero stream padding is used, the aligned dimension matches the vector size"
                            tens_trans.tens_trans_spec.conv_cfg = cnn_p.conv_cfg_t(conv_stride_0=0,conv_stride_1=0, conv_padding_0=trans['res_stream_padding'], conv_padding_1=0)
                            tens_res_dims = eq_mtx_dim(trans['res_dim'], tens_gen.layout)
                        if('src_name' in trans): #C2H stream
                            #extract use set
                            tens_use = find_by_name(tens_live_set_prev, trans['src_name'])
                            tens_trans.tens_use_set.append(tens_use)

                            #set tensor operands name
                            tens_trans.src_a_name = trans['src_name']

                            #set specification 
                            assert trans['src_stream_padding'] <= cnn_p.C_VECT_SIZE, "Error, input padding shall not be larger than vector size"
                            assert trans['src_stream_padding'] > 0 and get_align_dim(tens_use.dims, tens_use.layout) == cnn_p.C_VECT_SIZE or trans['src_stream_padding'] == 0, "Error, if non-zero stream padding is used, the aligned dimension match the vector size"
                            if('res_stream_padding' in trans):
                                tens_trans.tens_trans_spec.conv_cfg = cnn_p.conv_cfg_t(conv_stride_0=0,conv_stride_1=0, conv_padding_0=trans['res_stream_padding'], conv_padding_1=trans['src_stream_padding'])
                            else:
                                tens_trans.tens_trans_spec.conv_cfg = cnn_p.conv_cfg_t(conv_stride_0=0,conv_stride_1=0, conv_padding_0=0, conv_padding_1=trans['src_stream_padding'])
                            tens_src_a_dims = eq_mtx_dim(tens_use.dims, tens_use.layout)
                        tens_trans.tens_trans_spec.mtx_trans_dims = cnn_p.mtx_trans_dims_t(tens_src_a_dims=cnn_p.mtx_trans_dim_t(tens_src_a_dims[0], tens_src_a_dims[1]), tens_src_b_dims=cnn_p.mtx_trans_dim_t(0, 0), tens_res_dims=cnn_p.mtx_trans_dim_t(tens_res_dims[0], tens_res_dims[1])) 
                    case 'TRANS_LIN':
                        #set specification 
                        tens_trans.tens_trans_spec.tens_trans_type = cnn_p.tens_trans_type_t.TRANS_LIN
                        tens_trans.tens_trans_spec.nlin_f_type = cnn_p.nlin_f_type_t[trans['nlin_f_type'].upper()]
                        tens_trans.tens_trans_spec.bias_en = trans['bias_en']
                        tens_trans.tens_trans_spec.batch_norm_en = trans['batch_norm_en']
                        tens_trans.tens_trans_spec.repl_bias = trans['repl_bias']

                        tens_src_a = find_by_name(tens_live_set_prev, trans['src_a_name'])
                        tens_src_b = find_by_name(tens_live_set_prev, trans['src_b_name'])
                        if(tens_trans.tens_trans_spec.bias_en):
                            tens_bias  = find_by_name(tens_live_set_prev, trans['bias_name'])
                        if(tens_trans.tens_trans_spec.batch_norm_en):
                            tens_batch = find_by_name(tens_live_set_prev, trans['batch_name'])

                        #extract use set
                        tens_trans.tens_use_set.append(tens_src_a)
                        assert tens_src_a.layout == cnn_p.layout_t.ROW_FIRST, "Error, layout of source A in lin. trans. shall be row-first"
                        
                        tens_trans.tens_use_set.append(tens_src_b)
                        assert tens_src_b.layout == cnn_p.layout_t.COL_FIRST, "Error, layout of source B in lin. trans. shall be column-first"
                        if(trans['bias_en']):
                            tens_trans.tens_use_set.append(tens_bias)
                            assert tens_bias.layout == cnn_p.layout_t.COL_FIRST, "Error, layout of bias in lin. trans. shall be column-first"
                        if(trans['batch_norm_en']):
                            tens_trans.tens_use_set.append(tens_batch)
                            assert tens_batch.layout == cnn_p.layout_t.COL_FIRST, "Error, layout of batch norm params in lin. trans. shall be column-first"

                        #set tensor operands name
                        tens_trans.src_a_name = trans['src_a_name']
                        tens_trans.src_b_name = trans['src_b_name']
                        if(trans['bias_en']):
                            tens_trans.bias_name = trans['bias_name']
                        if(trans['batch_norm_en']):
                            tens_trans.batch_name = trans['batch_name']
                        tens_trans.res_name = trans['res_name']

                        assert len(tens_src_a.dims) == 2, "Error, only 2D, row first inputs are allowed for source A in linear transformation"
                        assert tens_src_a.dims[0] % cnn_p.C_VECT_SIZE == 0, "Error, source A in lin. trans. shall have all dimensions divisible by vector size"
                        tens_src_a_dims = cnn_p.mtx_trans_dim_t(tens_0_dim=tens_src_a.dims[0] // cnn_p.C_VECT_SIZE, tens_1_dim=tens_src_a.dims[1] // cnn_p.C_VECT_SIZE)
                        #verify source B dimensions - rows have to match A columns, if source B is 3D or 4D, than it will be flattened to 2D
                        if(len(tens_src_b.dims) == 2):
                            tens_src_b_flat_dims = tens_src_b.dims
                        elif(len(tens_src_b.dims) == 3):
                            tens_src_b_flat_dims = (tens_src_b.dims[0]*tens_src_b.dims[1]*tens_src_b.dims[2], 1)
                        else:
                            tens_src_b_flat_dims = (tens_src_b.dims[0]*tens_src_b.dims[1]*tens_src_b.dims[2], tens_src_b.dims[3])
                        assert tens_src_b_flat_dims[0] == tens_src_a.dims[1], "Error, source B shall be column first and its rows shall match src A columns in lin. trans."
                        tens_src_b_dims = cnn_p.mtx_trans_dim_t(tens_0_dim=tens_src_b_flat_dims[0] // cnn_p.C_VECT_SIZE, tens_1_dim=tens_src_b_flat_dims[1])
                        if(tens_trans.tens_trans_spec.bias_en):
                            if(tens_trans.tens_trans_spec.repl_bias):
                                assert tens_bias.dims[0] == tens_src_a.dims[0] and tens_bias.dims[1] == 1, "Error, bias rows shall shall match source A rows there shall be single column in lin. trans."
                            else:
                                assert tens_bias.dims[0] == tens_src_a.dims[0] and tens_bias.dims[1] == tens_src_b_flat_dims[1], "Error, bias rows shall shall match source A rows and source B columns lin. trans."
                        if(tens_trans.tens_trans_spec.batch_norm_en):
                            assert tens_batch.dims[0] == tens_src_a.dims[0] and tens_batch.dims[1] == 2, "Error, batch norm params shall match source A rows and there shall be two columns in lin. trans."
                        tens_res_dims = cnn_p.mtx_trans_dim_t(tens_0_dim=tens_src_a.dims[0] // cnn_p.C_VECT_SIZE, tens_1_dim=tens_src_b_flat_dims[1])
                        #write the extracted dimensions
                        tens_trans.tens_trans_spec.mtx_trans_dims = cnn_p.mtx_trans_dims_t(tens_src_a_dims=tens_src_a_dims, tens_src_b_dims=tens_src_b_dims, tens_res_dims=tens_res_dims)

                        #extract gen set
                        tens_gen.dims = (tens_src_a.dims[0], tens_src_b_flat_dims[1])
                        tens_gen.layout = cnn_p.layout_t.COL_FIRST
                        tens_gen.name = trans['res_name']
                        tens_trans.tens_gen_set.append(tens_gen)
                    case 'TRANS_CONV':
                        #set specification 
                        tens_trans.tens_trans_spec.tens_trans_type = cnn_p.tens_trans_type_t.TRANS_CONV
                        tens_trans.tens_trans_spec.nlin_f_type = cnn_p.nlin_f_type_t[trans['nlin_f_type'].upper()]
                        tens_trans.tens_trans_spec.bias_en = trans['bias_en']
                        tens_trans.tens_trans_spec.batch_norm_en = trans['batch_norm_en']
                        tens_trans.tens_trans_spec.repl_bias = trans['repl_bias']
                        tens_trans.tens_trans_spec.conv_cfg = cnn_p.conv_cfg_t(conv_stride_0=trans['stride'][0], conv_stride_1=trans['stride'][1], conv_padding_0=trans['padding'][0], conv_padding_1=trans['padding'][1])

                        tens_src_a = find_by_name(tens_live_set_prev, trans['src_a_name'])
                        tens_src_b = find_by_name(tens_live_set_prev, trans['src_b_name'])
                        if(tens_trans.tens_trans_spec.bias_en):
                            tens_bias  = find_by_name(tens_live_set_prev, trans['bias_name'])
                        if(tens_trans.tens_trans_spec.batch_norm_en):
                            tens_batch = find_by_name(tens_live_set_prev, trans['batch_name'])

                        #extract use set
                        tens_trans.tens_use_set.append(tens_src_a)
                        assert tens_src_a.layout == cnn_p.layout_t.ROW_FIRST, "Error, layout of source A in lin. trans. shall be row-first"
                        
                        tens_trans.tens_use_set.append(tens_src_b)
                        assert tens_src_b.layout == cnn_p.layout_t.COL_FIRST, "Error, layout of source B in lin. trans. shall be column-first"
                        if(trans['bias_en']):
                            tens_trans.tens_use_set.append(tens_bias)
                            assert tens_bias.layout == cnn_p.layout_t.COL_FIRST, "Error, layout of bias in lin. trans. shall be column-first"
                        if(trans['batch_norm_en']):
                            tens_trans.tens_use_set.append(tens_batch)
                            assert tens_batch.layout == cnn_p.layout_t.COL_FIRST, "Error, layout of batch norm params in lin. trans. shall be column-first"
            
                        #set tensor operands name
                        tens_trans.src_a_name = trans['src_a_name']
                        tens_trans.src_b_name = trans['src_b_name']
                        if(trans['bias_en']):
                            tens_trans.bias_name = trans['bias_name']
                        if(trans['batch_norm_en']):
                            tens_trans.batch_name = trans['batch_name']
                        tens_trans.res_name = trans['res_name']

                        #output tensor dimensions
                        tens_out_dim_0, tens_out_dim_1 = cnn_m.comp_conv_dims(tens_src_b.dims, tens_src_a.dims, (trans['stride'][0], trans['stride'][1]), (trans['padding'][0], trans['padding'][1]))

                        assert len(tens_src_a.dims) == 4, "Error, only 4D inputs are allowed for source A in conv. trans."
                        assert tens_src_a.dims[2] % cnn_p.C_VECT_SIZE == 0 and tens_src_a.dims[3] % cnn_p.C_VECT_SIZE == 0, "Error, source A in conv. trans. shall have channel dimensions divisible by vector size"
                        tens_src_a_lin_dims  = cnn_p.mtx_trans_dim_t(tens_0_dim=tens_src_a.dims[3] // cnn_p.C_VECT_SIZE, tens_1_dim=(tens_src_a.dims[0] * tens_src_a.dims[1] * tens_src_a.dims[2])// cnn_p.C_VECT_SIZE)
                        tens_src_a_conv_dims = cnn_p.tens_trans_dim_t(tens_0_dim=tens_src_a.dims[0], tens_1_dim=tens_src_a.dims[1], tens_2_dim=tens_src_a.dims[2] // cnn_p.C_VECT_SIZE, tens_3_dim=tens_src_a.dims[3] // cnn_p.C_VECT_SIZE)
                        #verify source B dimensions - rows have to match A columns
                        assert tens_src_b.dims[2] == tens_src_a.dims[2], "Error, source B shall be column first and its channels shall match source A channels in conv. trans."
                        tens_src_b_lin_dims  = cnn_p.mtx_trans_dim_t(tens_0_dim=(tens_src_a.dims[0] * tens_src_a.dims[1] * tens_src_a.dims[2])// cnn_p.C_VECT_SIZE, tens_1_dim=(tens_out_dim_1 * tens_out_dim_0))
                        tens_src_b_conv_dims = cnn_p.tens_trans_dim_t(tens_0_dim=tens_src_b.dims[0], tens_1_dim=tens_src_b.dims[1], tens_2_dim=tens_src_b.dims[2] // cnn_p.C_VECT_SIZE, tens_3_dim=0)
                        if(tens_trans.tens_trans_spec.bias_en):
                            if(tens_trans.tens_trans_spec.repl_bias):
                                assert tens_bias.dims[0] == tens_src_a.dims[3] and tens_bias.dims[1] == 1, "Error, bias rows shall shall match source A channels there shall be single column in conv. trans."
                            else:
                                assert tens_bias.dims[0] == tens_src_a.dims[3] and tens_bias.dims[1] == tens_src_b_lin_dims.tens_1_dim, "Error, bias rows shall shall match source A channels and result columns in conv. trans."
                        if(tens_trans.tens_trans_spec.batch_norm_en):
                            assert tens_batch.dims[0] == tens_src_a.dims[3] and tens_batch.dims[1] == 2, "Error, batch norm params shall match source A channels and there shall be two columns in conv. trans."
                        tens_res_lin_dims    = cnn_p.mtx_trans_dim_t(tens_0_dim=tens_src_a_lin_dims.tens_0_dim, tens_1_dim=tens_src_b_lin_dims.tens_1_dim)
                        tens_res_conv_dims = cnn_p.tens_trans_dim_t(tens_0_dim=tens_out_dim_0, tens_1_dim=tens_out_dim_1, tens_2_dim=tens_src_a.dims[3] // cnn_p.C_VECT_SIZE, tens_3_dim=0)
                        
                        #write the extracted dimensions
                        tens_trans.tens_trans_spec.mtx_trans_dims = cnn_p.mtx_trans_dims_t(tens_src_a_dims=tens_src_a_lin_dims, tens_src_b_dims=tens_src_b_lin_dims, tens_res_dims=tens_res_lin_dims)
                        tens_trans.tens_trans_spec.tens_trans_dims = cnn_p.tens_trans_dims_t(tens_src_a_dims=tens_src_a_conv_dims, tens_src_b_dims=tens_src_b_conv_dims, tens_res_dims=tens_res_conv_dims)

                        #extract gen set
                        tens_gen.dims = (tens_out_dim_0, tens_out_dim_1, tens_src_a.dims[3])
                        tens_gen.layout = cnn_p.layout_t.COL_FIRST
                        tens_gen.name = trans['res_name']
                        tens_trans.tens_gen_set.append(tens_gen)
                    case 'TRANS_MAXPOOL':
                        #set specification 
                        tens_trans.tens_trans_spec.tens_trans_type = cnn_p.tens_trans_type_t.TRANS_MAXPOOL
                        tens_trans.tens_trans_spec.conv_cfg = cnn_p.conv_cfg_t(conv_stride_0=trans['stride'][0], conv_stride_1=trans['stride'][1], conv_padding_0=trans['padding'][0], conv_padding_1=trans['padding'][1])

                        tens_src_b = find_by_name(tens_live_set_prev, trans['src_name'])

                        #extract use set
                        tens_trans.tens_use_set.append(tens_src_b)
                        assert tens_src_b.layout == cnn_p.layout_t.COL_FIRST, "Error, layout of source maxpool trans. shall be col-first"

                        #set tensor operands name
                        tens_trans.src_a_name = 'maxpool_kern'
                        tens_trans.src_b_name = trans['src_name']
                        tens_trans.res_name = trans['res_name']

                        #output tensor dimensions
                        kern_size_0 = trans['kern_size'][0]
                        kern_size_1 = trans['kern_size'][1]

                        tens_out_dim_0, tens_out_dim_1 = cnn_m.comp_conv_dims(tens_src_b.dims, (kern_size_0, kern_size_1), (trans['stride'][0], trans['stride'][1]), (trans['padding'][0], trans['padding'][1]))

                        assert tens_src_b.dims[2] % cnn_p.C_VECT_SIZE == 0, "Error, source in maxpool trans. shall have channel dimensions divisible by vector size"
                        tens_src_a_lin_dims  = cnn_p.mtx_trans_dim_t(tens_0_dim=0, tens_1_dim=0)
                        tens_src_a_conv_dims = cnn_p.tens_trans_dim_t(tens_0_dim=kern_size_0, tens_1_dim=kern_size_1, tens_2_dim=0, tens_3_dim=0)
                        tens_src_b_lin_dims  = cnn_p.mtx_trans_dim_t(tens_0_dim=(kern_size_0 * kern_size_1 * tens_src_b.dims[2])// cnn_p.C_VECT_SIZE, tens_1_dim=(tens_out_dim_1 * tens_out_dim_0))
                        tens_src_b_conv_dims = cnn_p.tens_trans_dim_t(tens_0_dim=tens_src_b.dims[0], tens_1_dim=tens_src_b.dims[1], tens_2_dim=tens_src_b.dims[2] // cnn_p.C_VECT_SIZE, tens_3_dim=0)
                        tens_res_lin_dims    = cnn_p.mtx_trans_dim_t(tens_0_dim=tens_src_b_conv_dims.tens_2_dim, tens_1_dim=tens_src_b_lin_dims.tens_1_dim)
                        tens_res_conv_dims   = cnn_p.tens_trans_dim_t(tens_0_dim=tens_out_dim_0, tens_1_dim=tens_out_dim_1, tens_2_dim=tens_src_b.dims[2] // cnn_p.C_VECT_SIZE, tens_3_dim=0)
                        
                        #write the extracted dimensions
                        tens_trans.tens_trans_spec.mtx_trans_dims = cnn_p.mtx_trans_dims_t(tens_src_a_dims=tens_src_a_lin_dims, tens_src_b_dims=tens_src_b_lin_dims, tens_res_dims=tens_res_lin_dims)
                        tens_trans.tens_trans_spec.tens_trans_dims = cnn_p.tens_trans_dims_t(tens_src_a_dims=tens_src_a_conv_dims, tens_src_b_dims=tens_src_b_conv_dims, tens_res_dims=tens_res_conv_dims)

                        #extract gen set
                        tens_gen.dims = (tens_out_dim_0, tens_out_dim_1, tens_src_b.dims[2])
                        tens_gen.layout = cnn_p.layout_t.COL_FIRST
                        tens_gen.name = trans['res_name']
                        tens_trans.tens_gen_set.append(tens_gen)
                    case _:
                        assert False, f"Error, unsupported tensor transformation type: {trans['tens_trans_type']}"

                #update live set: live_set(i) = live_set(i-1) + gen_set(i) - dealloc(i)
                if(tens_live_set_prev != None):
                  #verify that there is no ambiguity
                  assert not any(tens_n.name == tens_p.name for tens_n in tens_trans.tens_live_set for tens_p in tens_live_set_prev), "Error, conflict in variables names"
                  tens_trans.tens_live_set = tens_trans.tens_live_set + tens_live_set_prev

                tens_trans.tens_live_set = tens_trans.tens_gen_set + tens_trans.tens_live_set
                tens_trans.tens_live_set = [tens for tens in tens_trans.tens_live_set if tens.name not in trans['dealloc']]

                #push into the list of transformations
                tens_trans_seq.tens_trans_set.append(tens_trans) 

            #push into list of sequences
            tens_trans_seq_lst.append(tens_trans_seq)
    print("Internal representation generated\n")
    return tens_trans_seq_lst

def modify_addr(addr_tuple, pos, val):
    lst = list(addr_tuple)
    lst[pos] = val
    addr_tuple = cnn_p.tens_trans_addrs_t(*lst)
    return addr_tuple

def comp_tens_mem_size(tens, padding=0, norm=True): #how many words (vectors) does the tensor span in the accelerator's memory
    eq_mtx_dims = np.array(list(eq_mtx_dim(tens.dims, tens.layout, norm, padding)))
    return int(np.prod(eq_mtx_dims))

def mem_lin_alloc(tens_trans_seq_lst): #pass through the sequence and allocate memory for the tensors
    mem_alloc = cnn_p.mem_alloc_t(cnn_p.C_MMEM_SIZE)
    tens_live_prev = [] #tensors alive in previous transformation
    tens_alloc = [] #tensors to be allocated (not alive in previous, alive in current)
    tens_dealloc = [] #tensors to be deallocated (alive in previous, not alive in current)

    print("Allocating memory for the tensors\n")

    for seq in tens_trans_seq_lst:
        for tens_trans in seq.tens_trans_set:
            tens_alloc = [tens for tens in tens_trans.tens_live_set if tens not in tens_live_prev]
            for tens_a in tens_alloc:
               tens_a.block_index, tens_a.addr = mem_alloc.allocate(comp_tens_mem_size(tens_a))
            tens_dealloc = [tens for tens in tens_live_prev if tens not in tens_trans.tens_live_set]
            for tens_d in tens_dealloc:
                mem_alloc.deallocate(tens_d.block_index)

            #update the addresses in specs
            if(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_STREAM):
                if(tens_trans.tens_trans_spec.mtx_trans_dims.tens_res_dims != cnn_p.mtx_trans_dim_t(0, 0)): #H2C
                    tens_trans.tens_trans_spec.tens_trans_addrs = modify_addr(tens_trans.tens_trans_spec.tens_trans_addrs, 4, find_by_name(tens_trans.tens_live_set, tens_trans.res_name).addr)
                if(tens_trans.tens_trans_spec.mtx_trans_dims.tens_src_a_dims != cnn_p.mtx_trans_dim_t(0, 0)): #C2H
                    tens_trans.tens_trans_spec.tens_trans_addrs = modify_addr(tens_trans.tens_trans_spec.tens_trans_addrs, 0, find_by_name(tens_live_prev, tens_trans.src_a_name).addr)
            elif(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_LIN or tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_CONV):
                tens_trans.tens_trans_spec.tens_trans_addrs = modify_addr(tens_trans.tens_trans_spec.tens_trans_addrs, 0, find_by_name(tens_live_prev, tens_trans.src_a_name).addr)
                tens_trans.tens_trans_spec.tens_trans_addrs = modify_addr(tens_trans.tens_trans_spec.tens_trans_addrs, 1, find_by_name(tens_live_prev, tens_trans.src_b_name).addr)
                if(tens_trans.tens_trans_spec.bias_en):
                    tens_trans.tens_trans_spec.tens_trans_addrs = modify_addr(tens_trans.tens_trans_spec.tens_trans_addrs, 3, find_by_name(tens_live_prev, tens_trans.bias_name).addr)
                if(tens_trans.tens_trans_spec.batch_norm_en):
                    tens_trans.tens_trans_spec.tens_trans_addrs = modify_addr(tens_trans.tens_trans_spec.tens_trans_addrs, 2, find_by_name(tens_live_prev, tens_trans.batch_name).addr)
                tens_trans.tens_trans_spec.tens_trans_addrs = modify_addr(tens_trans.tens_trans_spec.tens_trans_addrs, 4, find_by_name(tens_trans.tens_live_set, tens_trans.res_name).addr)
            else:
                tens_trans.tens_trans_spec.tens_trans_addrs = modify_addr(tens_trans.tens_trans_spec.tens_trans_addrs, 1, find_by_name(tens_live_prev, tens_trans.src_b_name).addr)
                tens_trans.tens_trans_spec.tens_trans_addrs = modify_addr(tens_trans.tens_trans_spec.tens_trans_addrs, 4, find_by_name(tens_trans.tens_live_set, tens_trans.res_name).addr)
            tens_live_prev = tens_trans.tens_live_set
    
    print("Done with allocating memory for the tensors\n")

def gen_mm_trans(tens_trans_seq_lst, sim_mm_file_path, driver_mm_config_file_path):

    print("Generating memory-mapped transactions\n")
    
    with open(os.path.join(os.getcwd(), sim_mm_file_path), 'wb') as file_bin:
        with open(os.path.join(os.getcwd(), driver_mm_config_file_path), 'w') as file_driver:
            #setup regmap
            regmap = cnn_r.RegMap(cnn_r.interface(2**cnn_p.C_REGMAP_ADDR_WDT, file_bin, file_driver)) 
            #initialize regs
            ctrl_reg                            = cnn_r._RegCnn_accel_ctrl_reg(regmap)
            stat_reg                            = cnn_r._RegCnn_accel_stat_reg(regmap)
            int_reg                             = cnn_r._RegCnn_accel_int_reg(regmap)
            mmem_offset_reg                     = cnn_r._RegCnn_accel_mmem_offset_reg(regmap)
            gp_rw_reg                           = cnn_r._RegCnn_accel_gp_rw_reg(regmap)
            perf_run_ctrl_reg                   = cnn_r._RegCnn_accel_perf_run_ctrl_reg(regmap)
            perf_run_lh_reg                     = cnn_r._RegCnn_accel_perf_run_lh_reg(regmap)
            perf_run_uh_reg                     = cnn_r._RegCnn_accel_perf_run_uh_reg(regmap)
            perf_comp_ctrl_reg                  = cnn_r._RegCnn_accel_perf_comp_ctrl_reg(regmap)
            perf_comp_lh_reg                    = cnn_r._RegCnn_accel_perf_comp_lh_reg(regmap)
            perf_comp_uh_reg                    = cnn_r._RegCnn_accel_perf_comp_uh_reg(regmap)
            perf_stream_c2h_ctrl_reg            = cnn_r._RegCnn_accel_perf_stream_c2h_ctrl_reg(regmap)
            perf_stream_c2h_lh_reg              = cnn_r._RegCnn_accel_perf_stream_c2h_lh_reg(regmap)
            perf_stream_c2h_uh_reg              = cnn_r._RegCnn_accel_perf_stream_c2h_uh_reg(regmap)
            perf_stream_h2c_ctrl_reg            = cnn_r._RegCnn_accel_perf_stream_h2c_ctrl_reg(regmap)
            perf_stream_h2c_lh_reg              = cnn_r._RegCnn_accel_perf_stream_h2c_lh_reg(regmap)
            perf_stream_h2c_uh_reg              = cnn_r._RegCnn_accel_perf_stream_h2c_uh_reg(regmap)
            perf_cache_stall_ctrl_reg           = cnn_r._RegCnn_accel_perf_cache_stall_ctrl_reg(regmap)
            perf_cache_stall_lh_reg             = cnn_r._RegCnn_accel_perf_cache_stall_lh_reg(regmap)
            perf_cache_stall_uh_reg             = cnn_r._RegCnn_accel_perf_cache_stall_uh_reg(regmap)       
            tens_trans_cfg_reg                  = cnn_r._RegCnn_accel_tens_trans_cfg_reg(regmap)
            tens_trans_conv_cfg_reg             = cnn_r._RegCnn_accel_tens_trans_conv_cfg_reg(regmap)
            tens_trans_addr_src_a_reg           = cnn_r._RegCnn_accel_tens_trans_addr_src_a_reg(regmap)
            tens_trans_addr_src_b_reg           = cnn_r._RegCnn_accel_tens_trans_addr_src_b_reg(regmap)
            tens_trans_addr_batch_norm_reg      = cnn_r._RegCnn_accel_tens_trans_addr_batch_norm_reg(regmap)
            tens_trans_addr_bias_reg            = cnn_r._RegCnn_accel_tens_trans_addr_bias_reg(regmap)
            tens_trans_addr_res_reg             = cnn_r._RegCnn_accel_tens_trans_addr_res_reg(regmap)
            tens_trans_lin_dims_src_a_reg       = cnn_r._RegCnn_accel_tens_trans_lin_dims_src_a_reg(regmap)
            tens_trans_lin_dims_src_b_reg       = cnn_r._RegCnn_accel_tens_trans_lin_dims_src_b_reg(regmap)
            tens_trans_lin_dims_res_reg         = cnn_r._RegCnn_accel_tens_trans_lin_dims_res_reg(regmap)
            tens_trans_conv_dims_src_a_0_reg    = cnn_r._RegCnn_accel_tens_trans_conv_dims_src_a_0_reg(regmap)
            tens_trans_conv_dims_src_a_1_reg    = cnn_r._RegCnn_accel_tens_trans_conv_dims_src_a_1_reg(regmap)
            tens_trans_conv_dims_src_b_0_reg    = cnn_r._RegCnn_accel_tens_trans_conv_dims_src_b_0_reg(regmap)
            tens_trans_conv_dims_src_b_1_reg    = cnn_r._RegCnn_accel_tens_trans_conv_dims_src_b_1_reg(regmap)
            tens_trans_conv_dims_res_0_reg      = cnn_r._RegCnn_accel_tens_trans_conv_dims_res_0_reg(regmap)
            tens_trans_conv_dims_res_1_reg      = cnn_r._RegCnn_accel_tens_trans_conv_dims_res_1_reg(regmap)

            #set global variables performance counters, mem offset, etc.
            perf_run_ctrl_reg.perf_run_en           = 1
            perf_comp_ctrl_reg.perf_comp_en         = 1
            perf_stream_c2h_ctrl_reg.perf_stream_en = 1
            perf_stream_h2c_ctrl_reg.perf_stream_en = 1
            mmem_offset_reg.mmem_offset             = 64
            int_reg.int_stream_c2h_done_en          = 1
            int_reg.int_stream_h2c_done_en          = 1
            int_reg.int_tens_trans_seq_done_en      = 1
            gp_rw_reg.gp_rw = 0xDEADBEEF
            regmap._if.dump_state(regmap.CNN_ACCEL_MMEM_OFFSET_REG_ADDR, regmap.CNN_ACCEL_PERF_CACHE_STALL_UH_REG_ADDR)

            #print driver header
            file_driver.write(f"""\
/**
* @brief Memory-mapped writes to the accelerators regmap to configure it
*        for tensor transformation sequences 
*
* Auto-generated C driver header. Do not modify manually.
*
**/

#ifndef DRIVER_MM_CONFIG
#define DRIVER_MM_CONFIG

#include <stdint.h>
                  
""")

            #pass through all sequences, through all transformations and generate the needed MM trans
            for seq in tens_trans_seq_lst:
                tens_spec_offset = 0
                #print function definition
                file_driver.write(f"int {seq.name}_seq_mm_config() {{\n")
                for tens_trans in seq.tens_trans_set:
                    tens_trans_cfg_reg.tens_trans_type          = tens_trans.tens_trans_spec.tens_trans_type
                    tens_trans_cfg_reg.nlin_f_type              = tens_trans.tens_trans_spec.nlin_f_type
                    tens_trans_cfg_reg.batch_norm_en            = tens_trans.tens_trans_spec.batch_norm_en
                    tens_trans_cfg_reg.bias_en                  = tens_trans.tens_trans_spec.bias_en
                    tens_trans_cfg_reg.repl_bias                = tens_trans.tens_trans_spec.repl_bias
                    tens_trans_conv_cfg_reg.conv_stride_0       = tens_trans.tens_trans_spec.conv_cfg.conv_stride_0     
                    tens_trans_conv_cfg_reg.conv_stride_1       = tens_trans.tens_trans_spec.conv_cfg.conv_stride_1
                    tens_trans_conv_cfg_reg.conv_padding_0      = tens_trans.tens_trans_spec.conv_cfg.conv_padding_0      
                    tens_trans_conv_cfg_reg.conv_padding_1      = tens_trans.tens_trans_spec.conv_cfg.conv_padding_1
                    tens_trans_addr_src_a_reg.tens_addr         = tens_trans.tens_trans_spec.tens_trans_addrs.tens_src_a_addr
                    tens_trans_addr_src_b_reg.tens_addr         = tens_trans.tens_trans_spec.tens_trans_addrs.tens_src_b_addr
                    tens_trans_addr_batch_norm_reg.tens_addr    = tens_trans.tens_trans_spec.tens_trans_addrs.tens_batch_norm_addr
                    tens_trans_addr_bias_reg.tens_addr          = tens_trans.tens_trans_spec.tens_trans_addrs.tens_bias_addr
                    tens_trans_addr_res_reg.tens_addr           = tens_trans.tens_trans_spec.tens_trans_addrs.tens_res_addr
                    tens_trans_lin_dims_src_a_reg.tens_0_dim    = tens_trans.tens_trans_spec.mtx_trans_dims.tens_src_a_dims.tens_0_dim
                    tens_trans_lin_dims_src_a_reg.tens_1_dim    = tens_trans.tens_trans_spec.mtx_trans_dims.tens_src_a_dims.tens_1_dim
                    tens_trans_lin_dims_src_b_reg.tens_0_dim    = tens_trans.tens_trans_spec.mtx_trans_dims.tens_src_b_dims.tens_0_dim
                    tens_trans_lin_dims_src_b_reg.tens_1_dim    = tens_trans.tens_trans_spec.mtx_trans_dims.tens_src_b_dims.tens_1_dim
                    tens_trans_lin_dims_res_reg.tens_0_dim      = tens_trans.tens_trans_spec.mtx_trans_dims.tens_res_dims.tens_0_dim
                    tens_trans_lin_dims_res_reg.tens_1_dim      = tens_trans.tens_trans_spec.mtx_trans_dims.tens_res_dims.tens_1_dim
                    tens_trans_conv_dims_src_a_0_reg.tens_0_dim = tens_trans.tens_trans_spec.tens_trans_dims.tens_src_a_dims.tens_0_dim
                    tens_trans_conv_dims_src_a_0_reg.tens_1_dim = tens_trans.tens_trans_spec.tens_trans_dims.tens_src_a_dims.tens_1_dim
                    tens_trans_conv_dims_src_a_1_reg.tens_2_dim = tens_trans.tens_trans_spec.tens_trans_dims.tens_src_a_dims.tens_2_dim
                    tens_trans_conv_dims_src_a_1_reg.tens_3_dim = tens_trans.tens_trans_spec.tens_trans_dims.tens_src_a_dims.tens_3_dim
                    tens_trans_conv_dims_src_b_0_reg.tens_0_dim = tens_trans.tens_trans_spec.tens_trans_dims.tens_src_b_dims.tens_0_dim
                    tens_trans_conv_dims_src_b_0_reg.tens_1_dim = tens_trans.tens_trans_spec.tens_trans_dims.tens_src_b_dims.tens_1_dim
                    tens_trans_conv_dims_src_b_1_reg.tens_2_dim = tens_trans.tens_trans_spec.tens_trans_dims.tens_src_b_dims.tens_2_dim
                    tens_trans_conv_dims_src_b_1_reg.tens_3_dim = tens_trans.tens_trans_spec.tens_trans_dims.tens_src_b_dims.tens_3_dim
                    tens_trans_conv_dims_res_0_reg.tens_0_dim   = tens_trans.tens_trans_spec.tens_trans_dims.tens_res_dims.tens_0_dim
                    tens_trans_conv_dims_res_0_reg.tens_1_dim   = tens_trans.tens_trans_spec.tens_trans_dims.tens_res_dims.tens_1_dim
                    tens_trans_conv_dims_res_1_reg.tens_2_dim   = tens_trans.tens_trans_spec.tens_trans_dims.tens_res_dims.tens_2_dim
                    tens_trans_conv_dims_res_1_reg.tens_3_dim   = tens_trans.tens_trans_spec.tens_trans_dims.tens_res_dims.tens_3_dim
                    if(not (tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_CONV or tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_MAXPOOL)):
                        regmap._if.dump_state(regmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR, regmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR, False, tens_spec_offset, True)
                        tens_spec_offset = tens_spec_offset + (regmap.CNN_ACCEL_TENS_TRANS_LIN_DIMS_RES_REG_ADDR - regmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR + 4)
                    else:
                        regmap._if.dump_state(regmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR, regmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR, False, tens_spec_offset, True)
                        tens_spec_offset = tens_spec_offset + (regmap.CNN_ACCEL_TENS_TRANS_CONV_DIMS_RES_1_REG_ADDR - regmap.CNN_ACCEL_TENS_TRANS_CFG_REG_ADDR + 4)
                file_driver.write("return 1;\n}\n\n")
                ctrl_reg.tens_trans_seq_len = len(seq.tens_trans_set)
                ctrl_reg.tens_trans_seq_start = 1
                regmap._if.dump_state(regmap.CNN_ACCEL_CTRL_REG_ADDR, regmap.CNN_ACCEL_CTRL_REG_ADDR, True)

            file_driver.write("\n#endif DRIVER_MM_CONFIG\n")

    print("Done generating driver memory-mapped configuration, dumping output in: " + os.path.join(os.getcwd(), driver_mm_config_file_path) + "\n")
    print("Done generating memory-mapped transactions, dumping output in: " + os.path.join(os.getcwd(), sim_mm_file_path) + "\n")

def write_fxp_entry(file, fxp_entry):
    fxp_entry_bin_str = fxp_entry.bin()
    assert len(fxp_entry_bin_str) % 8 == 0, "Error: Value size must be byte multiple"
    fxp_entry_bytes = bytearray(int(fxp_entry_bin_str[i:i+8], 2) for i in range(0, len(fxp_entry_bin_str), 8))
    if(False): #TODO: could come in handy later
        fxp_entry_bytes = fxp_entry_bytes.reverse() 
    file.write(fxp_entry_bytes)

def flat_to_vect_lst(tens_data, tens):
    vect_lst = fxp(np.zeros((comp_tens_mem_size(tens), cnn_p.C_VECT_SIZE))).like(cnn_p.FXP_EXT_WORD)

    #first flatten to 2D matrix
    match len(tens.dims):
        case 2:
            tens_mtx = tens_data
        case 3:
            i, j, k = tens_data.shape
            tens_mtx = np.zeros((k, i * j))
            for x in range(k):
                tens_mtx[x, :] = tens_data[:, :, x].ravel()
        case 4:
            i, j, k, l = tens_data.shape
            tens_mtx = np.zeros((l, i * j * k))
            for x in range(l):
                tens_mtx[x, :] = tens_data[:, :, :, x].ravel()

    if(tens.layout == cnn_p.layout_t.ROW_FIRST):
        for y in range(tens_mtx.shape[1] // cnn_p.C_VECT_SIZE):
            for x in range(tens_mtx.shape[0]):
                vect_lst[y * tens_mtx.shape[0] + x, :] = tens_mtx[x, cnn_p.C_VECT_SIZE * y : cnn_p.C_VECT_SIZE * (y + 1)]
    else:
        for x in range(tens_mtx.shape[0] // cnn_p.C_VECT_SIZE):  
            for y in range(tens_mtx.shape[1]):
                vect_lst[x * tens_mtx.shape[1] + y, :] = tens_mtx[cnn_p.C_VECT_SIZE * x : cnn_p.C_VECT_SIZE * (x + 1), y]  

    return vect_lst


def gen_stream_trans(tens_trans_seq_lst, sim_in_stream_file_path):

    print("Generating stream transactions\n")

    h2c_trans_lst = []
    c2h_trans_lst = []
    h2c_offset = 0
    c2h_offset = 0

    with open(os.path.join(os.getcwd(), sim_in_stream_file_path), 'wb') as file:
        for seq in tens_trans_seq_lst:
            for tens_trans in seq.tens_trans_set:
                if(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_STREAM):
                    if(tens_trans.res_name): #H2C
                        #load/generate data
                        h2c_tens  = tens_trans.tens_gen_set[0]
                        tens_fxp, tens_real = cnn_m.load_tens_data(h2c_tens, tens_trans.h2c_data_source, tens_trans.tens_trans_spec.conv_cfg.conv_padding_0)

                        #flatten to array of vectors
                        vect_lst = flat_to_vect_lst(tens_fxp, h2c_tens)

                        #write to file in order
                        for vect in vect_lst:
                            for index, value in enumerate(vect):
                                if(index < cnn_p.C_VECT_SIZE - tens_trans.tens_trans_spec.conv_cfg.conv_padding_0): #write only non-padding values
                                    write_fxp_entry(file, value)

                        h2c_len = comp_tens_mem_size(tens=h2c_tens, padding=tens_trans.tens_trans_spec.conv_cfg.conv_padding_0, norm=False) * cnn_p.C_ARITH_FXP_EXT_BYTE_LEN

                        #contruct the H2C transfer object
                        h2c_trans = cnn_p.stream_trans_t(data_real=tens_real, data_accel=tens_fxp, name=h2c_tens.name, offset=h2c_offset, len=h2c_len)
                        h2c_offset = h2c_offset + h2c_len
                        h2c_trans_lst.append(h2c_trans)
                    if(tens_trans.src_a_name): #C2H
                        c2h_len = comp_tens_mem_size(tens=tens_trans.tens_use_set[0], padding=tens_trans.tens_trans_spec.conv_cfg.conv_padding_0, norm=False) * cnn_p.C_ARITH_FXP_EXT_BYTE_LEN
                        #initialize the C2H transfer object
                        c2h_trans = cnn_p.stream_trans_t(data_real=None, data_accel=None, name=tens_trans.src_a_name, offset=c2h_offset, len=c2h_len)
                        c2h_offset = c2h_offset + c2h_len #update offset
                        c2h_trans_lst.append(c2h_trans)

        print("Done generating stream transactions, dumping output in: " + os.path.join(os.getcwd(), sim_in_stream_file_path) + "\n")
        return h2c_trans_lst, c2h_trans_lst
    
def gen_ctrl(tens_trans_seq_lst, h2c_trans_lst, c2h_trans_lst, sim_ctrl_path):

    print("Generating simulation control info\n")

    h2c_index = 0
    c2h_index = 0
    with open(os.path.join(os.getcwd(), sim_ctrl_path), 'w') as file:
        for seq in tens_trans_seq_lst:
            for tens_trans in seq.tens_trans_set:
                if(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_STREAM):
                    if(tens_trans.res_name): #H2C
                        assert h2c_trans_lst[h2c_index].name == tens_trans.res_name, "Error, the H2C tensor names shall match"
                        file.write(f"H2C , {h2c_trans_lst[h2c_index].offset} , {h2c_trans_lst[h2c_index].len} , {h2c_trans_lst[h2c_index].name} , {tens_trans_seq_lst.index(seq)}\n")
                        h2c_index = h2c_index + 1
                    if(tens_trans.src_a_name): #C2H
                        assert c2h_trans_lst[c2h_index].name == tens_trans.src_a_name, "Error, the C2H tensor names shall match"
                        file.write(f"C2H , {c2h_trans_lst[c2h_index].offset} , {c2h_trans_lst[c2h_index].len} , {c2h_trans_lst[c2h_index].name} , {tens_trans_seq_lst.index(seq)}\n")
                        c2h_index = c2h_index + 1
        print("Done generating simulation control info, dumping output in: " + os.path.join(os.getcwd(), sim_ctrl_path) + "\n")

def read_bytes_to_bin_string(file, byte_len, byte_offset, rev_endian=False, b_prefix=True):
    file.seek(byte_offset)
    byte_data = file.read(byte_len)
    if rev_endian:
        byte_data = byte_data[::-1]
    #convert bytes to a binary string
    bin_string = ''.join(f'{byte:08b}' for byte in byte_data)

    if(b_prefix):
        bin_string = '0b' + bin_string        
    
    return bin_string

def insert_dot(fxp_bin, frac_wdt):
    if frac_wdt < 0 or frac_wdt > len(fxp_bin):
        raise ValueError("frac_wdt must be a positive integer within the length of the string")
    pos_from_left = len(fxp_bin) - frac_wdt
    result = fxp_bin[:pos_from_left] + '.' + fxp_bin[pos_from_left:]
    
    return result

def constr_tens(vect_lst, tens):
    tens_eq_mtx_fxp  = fxp(np.zeros(eq_mtx_dim(tens.dims, tens.layout, False))).like(cnn_p.FXP_EXT_WORD)

    #construct 2D tensor from the vector list first
    if(tens.layout == cnn_p.layout_t.ROW_FIRST):
        for y in range(tens_eq_mtx_fxp.shape[1] // cnn_p.C_VECT_SIZE):
            for x in range(tens_eq_mtx_fxp.shape[0]):
                tens_eq_mtx_fxp[x, cnn_p.C_VECT_SIZE * y : cnn_p.C_VECT_SIZE * (y + 1)]   = vect_lst[y * tens_eq_mtx_fxp.shape[0] + x, :]
    else:
        for x in range(tens_eq_mtx_fxp.shape[0] // cnn_p.C_VECT_SIZE):  
            for y in range(tens_eq_mtx_fxp.shape[1]):                       
                tens_eq_mtx_fxp[cnn_p.C_VECT_SIZE * x : cnn_p.C_VECT_SIZE * (x + 1), y]   = vect_lst[x * tens_eq_mtx_fxp.shape[1] + y, :]

    #reshape
    match len(tens.dims):
        case 2:
            tens_data = tens_eq_mtx_fxp
        case 3:
            tens_temp = np.array(tens_eq_mtx_fxp)
            tens_temp = tens_temp.T.reshape(tens.dims)
            tens_data = fxp(tens_temp).like(cnn_p.FXP_EXT_WORD)
        case 4: #TODO: verify if this is correct
            tens_temp = np.array(tens_eq_mtx_fxp)
            tens_temp = tens_temp.T.reshape(tens.dims)
            tens_data = fxp(tens_temp).like(cnn_p.FXP_EXT_WORD)

    return tens_data

def compar_tens(tens_approx_data, tens_ref_data, max_err=cnn_p.C_MAX_REL_ERR, plot_title="Approximation vs Reference - relative error"): #compare two tensors, one is reference tensor, the other is approximation tensor

    rel_err = abs((tens_approx_data - tens_ref_data)/(tens_ref_data + cnn_p.C_EPS)) #relative error matrix
    #plot histogram
    cnn_m.plot_hist(rel_err.flatten(), 20, plot_title)
    #max error test
    max_rel_err = rel_err > max_err
    for i, x in enumerate(max_rel_err.flatten()):
        if(x):
            print(f"[ERROR], reference model @ index {i} = {(tens_ref_data.flatten())[i]}, approximation output = {(tens_approx_data.flatten())[i]} relative absolute error = {rel_err.flatten()[i]} is larger than maximum allowed: {max_err}\n")
    print(f"Error statistics: Mean: {np.mean(rel_err)}, Standard deviation: {np.std(rel_err)}, Maximum: {rel_err.max()}, Minimum: {rel_err.min()}")
            

def read_c2h_bin(tens_trans_seq_lst, c2h_trans_lst, sim_out_stream_file_path):
    
    print("Reading the accelerator C2H stream, initializing the values")
    c2h_index = 0

    with open(os.path.join(os.getcwd(), sim_out_stream_file_path), 'rb') as file:
        for seq in tens_trans_seq_lst:
            for tens_trans in seq.tens_trans_set:
                if(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_STREAM):
                    if(tens_trans.src_a_name):
                        c2h_trans = c2h_trans_lst[c2h_index]
                        c2h_tens  = tens_trans.tens_use_set[0]

                        #read from file, create list of vectors
                        vect_lst = fxp(np.zeros((comp_tens_mem_size(c2h_tens), cnn_p.C_VECT_SIZE))).like(cnn_p.FXP_EXT_WORD)
                        off = 0
                        for i, vect in enumerate(vect_lst):
                            for j in range(len(vect)):
                                if(j < cnn_p.C_VECT_SIZE - tens_trans.tens_trans_spec.conv_cfg.conv_padding_1):
                                    vect_lst[i][j] = insert_dot(read_bytes_to_bin_string(file, cnn_p.C_ARITH_FXP_EXT_BYTE_LEN, c2h_trans.offset + off), cnn_p.C_ARITH_FXP_EXT_FRAC_WDT)
                                    off = off + cnn_p.C_ARITH_FXP_EXT_BYTE_LEN
                                else: #part of padding, initialize to zero now
                                    vect_lst[i][j] = fxp(0.0).like(cnn_p.FXP_EXT_WORD)

                        #construct tensor from list of vectors
                        tens_fxp = constr_tens(vect_lst, c2h_tens)
                        c2h_trans.data_accel = tens_fxp                                      
                        c2h_trans.data_real  = tens_fxp.real
                        c2h_index = c2h_index + 1

def compar_accel(tens_trans_seq_lst, c2h_trans_lst):

    print("Comparing accelerator output with the reduced-precision and real models")
    c2h_index = 0

    for seq in tens_trans_seq_lst:
        for tens_trans in seq.tens_trans_set:
            if(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_STREAM and tens_trans.src_a_name):
                #apply stream output padding
                c2h_tens = find_by_name(tens_trans.tens_use_set, tens_trans.src_a_name)
                cnn_m.tens_set_stream_padding(c2h_tens.data_real, c2h_tens.layout, tens_trans.tens_trans_spec.conv_cfg.conv_padding_1)
                cnn_m.tens_set_stream_padding(c2h_tens.data_accel, c2h_tens.layout, tens_trans.tens_trans_spec.conv_cfg.conv_padding_1)
                compar_tens(c2h_trans_lst[c2h_index].data_accel.real, fxp(c2h_tens.data_accel).like(cnn_p.FXP_EXT_WORD).real, cnn_p.C_MAX_REL_ERR, "Accelerator vs. Reduced Precision - Tensor: " + c2h_tens.name) 
                compar_tens(c2h_trans_lst[c2h_index].data_accel.real, c2h_tens.data_real, cnn_p.C_MAX_REL_ERR, "Accelerator vs. Real - Tensor: " + c2h_tens.name)
                c2h_index = c2h_index + 1

def compar_model(tens_trans_seq_lst):

    print("Comparing the reduced-precision and real model")

    for seq in tens_trans_seq_lst:
        for tens_trans in seq.tens_trans_set:
            if(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_STREAM and tens_trans.src_a_name):
                #apply stream output padding
                c2h_tens = find_by_name(tens_trans.tens_use_set, tens_trans.src_a_name)
                cnn_m.tens_set_stream_padding(c2h_tens.data_real, c2h_tens.layout, tens_trans.tens_trans_spec.conv_cfg.conv_padding_1)
                cnn_m.tens_set_stream_padding(c2h_tens.data_accel, c2h_tens.layout, tens_trans.tens_trans_spec.conv_cfg.conv_padding_1)
                compar_tens(fxp(c2h_tens.data_accel).like(cnn_p.FXP_EXT_WORD).real, c2h_tens.data_real, cnn_p.C_MAX_REL_ERR, "Reduced Precision vs Real - Tensor: " + c2h_tens.name) 

def model_comp(tens_trans_seq_lst, h2c_trans_lst): #computes the reduced-precision model inference, as well as the real reference

    print("Modelling the reduced-precision computations, generating expected C2H results")
    h2c_index = 0

    for seq in tens_trans_seq_lst:
        for tens_trans in seq.tens_trans_set:
            if(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_STREAM):
                if(tens_trans.res_name): #H2C, initialize, expand to internal precision
                    h2c_tens            = find_by_name(tens_trans.tens_gen_set, tens_trans.res_name)
                    h2c_tens.data_real  = h2c_trans_lst[h2c_index].data_real
                    h2c_tens.data_accel = fxp(h2c_trans_lst[h2c_index].data_accel).like(cnn_p.FXP_INT_WORD)
                    h2c_index = h2c_index + 1
            elif(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_MAXPOOL):
                src_b = find_by_name(tens_trans.tens_use_set, tens_trans.src_b_name)
                res = find_by_name(tens_trans.tens_gen_set, tens_trans.res_name)
                res.data_real  = cnn_m.tens_trans_maxpool(src=src_b, tens_trans_spec=tens_trans.tens_trans_spec, fxp_mode=False)
                res.data_accel = cnn_m.tens_trans_maxpool(src=src_b, tens_trans_spec=tens_trans.tens_trans_spec, fxp_mode=True)
            else:
                src_a = find_by_name(tens_trans.tens_use_set, tens_trans.src_a_name)
                src_b = find_by_name(tens_trans.tens_use_set, tens_trans.src_b_name)
                if(tens_trans.tens_trans_spec.batch_norm_en):
                    batch_norm = find_by_name(tens_trans.tens_use_set, tens_trans.batch_name)
                else:
                    batch_norm = cnn_p.tens_t() #empty object, will not be used
                if(tens_trans.tens_trans_spec.bias_en):
                    bias = find_by_name(tens_trans.tens_use_set, tens_trans.bias_name)
                else:
                    bias = cnn_p.tens_t() #empty object, will not be used
                res = find_by_name(tens_trans.tens_gen_set, tens_trans.res_name)
                if(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_LIN):
                    res.data_real = cnn_m.tens_trans_lin(src_a=src_a, src_b=src_b, tens_trans_spec=tens_trans.tens_trans_spec, batch_norm=batch_norm, bias=bias, fxp_mode=False)
                    res.data_accel = cnn_m.tens_trans_lin(src_a=src_a,src_b=src_b, tens_trans_spec=tens_trans.tens_trans_spec, batch_norm=batch_norm, bias=bias, fxp_mode=True)
                elif(tens_trans.tens_trans_spec.tens_trans_type == cnn_p.tens_trans_type_t.TRANS_CONV):
                    res.data_real = cnn_m.tens_trans_conv(src_a=src_a,src_b=src_b, tens_trans_spec=tens_trans.tens_trans_spec, batch_norm=batch_norm, bias=bias, fxp_mode=False)
                    res.data_accel = cnn_m.tens_trans_conv(src_a=src_a,src_b=src_b, tens_trans_spec=tens_trans.tens_trans_spec, batch_norm=batch_norm, bias=bias, fxp_mode=True)
                else:
                    assert False, "Error, not yet implemented"
                                
def gen_sim_in(model_descr_file_path, sim_mm_file_path, sim_in_stream_file_path, sim_ctrl_path, driver_mm_config_file_path):
    build()
    print("Generating simulation inputs\n")
    tens_trans_seq_lst = gen_inter_repr(model_descr_file_path) #generate internal representation
    mem_lin_alloc(tens_trans_seq_lst) #allocate addresses
    gen_mm_trans(tens_trans_seq_lst, sim_mm_file_path, driver_mm_config_file_path) #generate memory-mapped transactions
    h2c_trans_lst, c2h_trans_lst = gen_stream_trans(tens_trans_seq_lst, sim_in_stream_file_path) #generate H2C stream data
    gen_ctrl(tens_trans_seq_lst, h2c_trans_lst, c2h_trans_lst, sim_ctrl_path) #generate simulation control data

def proc_sim_out(model_descr_file_path, sim_in_stream_file_path, sim_out_stream_file_path):
    print("Processing simulation outputs\n")
    tens_trans_seq_lst = gen_inter_repr(model_descr_file_path) #generate internal representation
    mem_lin_alloc(tens_trans_seq_lst) #allocate addresses
    h2c_trans_lst, c2h_trans_lst = gen_stream_trans(tens_trans_seq_lst, sim_in_stream_file_path) #setup C2H stream data
    read_c2h_bin(tens_trans_seq_lst, c2h_trans_lst, sim_out_stream_file_path) #read the binary produced by accelerator, load the tensor values
    model_comp(tens_trans_seq_lst, h2c_trans_lst) #model the computation results in reduced precision
    compar_accel(tens_trans_seq_lst, c2h_trans_lst) #compare with reference

def proc_model(model_descr_file_path, sim_in_stream_file_path):
    print("Computing the reduced-precision model\n")
    tens_trans_seq_lst = gen_inter_repr(model_descr_file_path) #generate internal representation
    mem_lin_alloc(tens_trans_seq_lst) #allocate addresses
    h2c_trans_lst, _ = gen_stream_trans(tens_trans_seq_lst, sim_in_stream_file_path) #setup C2H stream data
    model_comp(tens_trans_seq_lst, h2c_trans_lst) #model the computation results in reduced precision, compare with reference
    compar_model(tens_trans_seq_lst)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate tanh LUT parser")

    #TODO autogenerate the default file paths
    #add the command line arguments
    parser.add_argument("mode",                                 nargs='?',  type=str, default="s_in",                   help="if 's_in' then we generate simulation inputs, if 's_out' we process simulation outputs")
    parser.add_argument("model_descr_file_path",                nargs='?',  type=str, default="test_model_spec.yaml",   help="Relative path to file which describes the models (tensor transformation sequences) to be simulated")
    parser.add_argument("sim_mm_file_path",                     nargs='?',  type=str, default="test_mm.bin",            help="Relative path to the file describing memory-mapped transactions")
    parser.add_argument("sim_in_stream_file_path",              nargs='?',  type=str, default="test_h2c_stream.bin",    help="Relative path to the file describing the stream inputs")
    parser.add_argument("sim_out_stream_file_path",             nargs='?',  type=str, default="test_c2h_stream.bin",    help="Relative path to the file describing the stream outputs")
    parser.add_argument("sim_ctrl_path",                        nargs='?',  type=str, default="test_ctrl.txt",          help="Relative path to the file with simulation flow metadata")
    parser.add_argument("driver_mm_config_file_path",           nargs='?',  type=str, default="test_driver.c",          help="Relative path the generated C driver for MM config")

    #parse the command line arguments
    args = parser.parse_args()
    if(args.mode == "s_in"):
        gen_sim_in(args.model_descr_file_path, args.sim_mm_file_path, args.sim_in_stream_file_path, args.sim_ctrl_path, args.driver_mm_config_file_path)
    elif(args.mode == "s_out"):
        proc_sim_out(args.model_descr_file_path, args.sim_in_stream_file_path, args.sim_out_stream_file_path)
    elif(args.mode == "m"):
        proc_model(args.model_descr_file_path, args.sim_in_stream_file_path)
    else:
        assert False, f"Error, invalid mode: {args.mode}"
