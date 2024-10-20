# CNN Accelerator Special Instructions Documentation

This document provides detailed information on the special computer instructions for a Convolutional Neural Network (CNN) accelerator. The instructions covered include `TENS_CONV`, `TENS_LIN`, `TENS_MAXPOOL`, and `TENS_STREAM`. Each instruction operates on a set of operand tensors and produces a single result tensor. In addition to operands, these instructions also have parameters such as the activation function, bias enable, batch normalization enable, padding, stride, and stream padding.

## 1. TENS_STREAM

The `TENS_STREAM` transformation performs a Host-To-Card (H2C) or Card-To-Host (C2H) or duplex data stream transfer.

### YAML Specification

| FIELD      | TYPE  | EXAMPLE  | DESCRIPTION  |
|------------|-------|----------|--------------|
|tens_trans_type|string|TENS_STREAM|Transformation identifier, shall be TENS_STREAM in this case.|
|src_name|string|c2h_tens|Name of the tensor to be sent to host (C2H). Can be left empty with all the subsequent C2H fields if no C2H is taking place.|
|src_description|string|this is an C2H tensor|optional comment|
|src_stream_padding|int|0|C2H stream padding. Only applicable if the aligned tensor dimension is equal t o SIMD vector width. Shall be less than SIMD vector width.|
|res_name|string|h2c_tens|Name of the tensor to be sent from host (H2C). This automatically allocates a new tensor in the main memory.|
|res_description|string|this is an H2C tensor|optional comment|
|res_stream_padding|int|0|H2C stream padding. Only applicable if the aligned tensor dimension is equal t o SIMD vector width. Shall be less than SIMD vector width.|
|layout|string|col_first|Memory layout of the H2C tensor. Shall be either col_first or row_first.|
|res_dim|list|[3, 3, 32, 32]|List of integers setting the dimensions of the H2C tensor. Tensors shall be either 2D,3D, or 4D. Based on the dimensionality and layout, certain dimensions shall be divisble by SIMD vector width.|
|h2c_data_source|string|rand_gauss|String which identifies what are the source values for the H2C tensor. Can be rand_gauss (data will be random gaussian distributed) or lin_index (data will be linearly incremented). Data can be also loaded from a CSV file which has to be located in the same folder as the script. Fromat is (file_name.csv)\(line_name). Example: cnn_weights.csv\lin_layer_0.weight. |
|dealloc|list|[h2c_tens, c2h_tens]|List of names of tensors to be deallocated after this operation.|

## 2. TENS_CONV

The `TENS_CONV` transformation performs a convolution operation on an input tensor with a weight tensor resulting in output tensor, optionally applying a bias and batch normalization tensor. Additional parameters are stride and padding. Channel_in and channel_out must be divisble by the SIMD vector width.

### YAML Specification

| FIELD      | TYPE  | EXAMPLE  | DESCRIPTION  |
|------------|-------|----------|--------------|
|tens_trans_type|string|TENS_CONV|Transformation identifier, shall be TENS_CONV in this case.|
|nlin_f_type|string|NLIN_F_RELU|Non-linear activation function identifier. Activation function is applied after batch normalization. Shall be NLIN_F_IDENTITY/NLIN_F_RELU/NLIN_F_TANH.|
|batch_norm_en|bool|True|Enables batch normalization. Applied after convolution.|
|bias_en|bool|True|Enables bias addition in the convolution operation.|
|repl_bias|bool|True|If set, the bias tensor is replicated across height and width in each channel. Else the bias is a general tensor of same dimensions as output tensor.|
|src_a_name|string|conv_weight_tens|Weight (filter mask) tensor name. Tensor shall have four dimensions:  (height_kern, width_kern, channel_in, channel_out). Tensor layout is row-first.|
|src_b_name|string|conv_in_tens|Input (input feature map) tensor name. Tensor shall have three dimensions: (height_in, width_in, channel_in). Tensor layout is column-first.|
|bias_name|string|conv_bias_tens|Bias tensor name. If bias is disabled, value is ignored. If replicate bias is enabled, tensor shall have two dimensions: (channel_out, 1). Else tensor shall have three dimensions: (height_out, width_out, channel_out). Tensor layout is column-first.|
|batch_name|string|conv_batch_tens|Batch normalization tensor name. If batch norm is disabled, value is ignored. Else tensor shall have two dimensions: (channel_out, 2). Tensor layout is column-first.|
|stride|list|[1, 2]|List of two integers. Sets the convolution stride parameters.|
|padding|list|[1, 2]|List of two integers. Sets the convolution padding parameters.|
|res_name|string|conv_out_tens|Name of the convolution output tensor. Has three dimensions: (height_out, width_out, channel_out). Tensor layout is column-first.|
|res_description|string|this is an output tensor|optional comment|
|dealloc|list|[conv_in_tens, conv_weight_tens]|List of names of tensors to be deallocated after this operation.|

## 3. TENS_LIN

The `TENS_LIN` transformation performs a linear layer operation on an input tensor with a weight tensor resulting in output tensor, optionally applying a bias and batch normalization tensor. N_in and n_out must be divisble by the SIMD vector width.

### YAML Specification

| FIELD      | TYPE  | EXAMPLE  | DESCRIPTION  |
|------------|-------|----------|--------------|
|tens_trans_type|string|TENS_LIN|Transformation identifier, shall be TENS_LIN in this case.|
|nlin_f_type|string|NLIN_F_RELU|Non-linear activation function identifier. Activation function is applied after batch normalization. Shall be NLIN_F_IDENTITY/NLIN_F_RELU/NLIN_F_TANH.|
|batch_norm_en|bool|True|Enables batch normalization. Applied after matrix-multiplication.|
|bias_en|bool|True|Enables bias addition in the linear layer operation.|
|repl_bias|bool|True|If set, the bias tensor is replicated across columns. Else the bias is a general tensor of same dimensions as output tensor.|
|src_a_name|string|lin_weight_tens|Weight tensor name. Tensor shall have two dimensions:  (n_out, n_in). Tensor layout is row-first.|
|src_b_name|string|lin_in_tens|Input (feature vector) tensor name. Tensor shall have two dimensions: (n_in, n_b). If the tensor has three dimensions: (height, width, channel_in), it will be flattened into a 2D tensor (height * width * channel_in, 1) = (n_in, n_b). Tensor layout is column-first.|
|bias_name|string|lin_bias_tens|Bias tensor name. If bias is disabled, value is ignored. If replicate bias is enabled, tensor shall have two dimensions: (n_out, 1). Else tensor shall have two dimensions: (n_out, n_b). Tensor layout is column-first.|
|batch_name|string|lin_batch_tens|Batch normalization tensor name. If batch norm is disabled, value is ignored. Else tensor shall have two dimensions: (n_out, 2). Tensor layout is column-first.|
|res_name|string|lin_out_tens|Name of the linear layer output tensor. Has two dimensions: (n_out, n_b). Tensor layout is column-first.|
|res_description|string|this is an output tensor|optional comment|
|dealloc|list|[lin_in_tens, lin_weight_tens]|List of names of tensors to be deallocated after this operation.|

## 4. TENS_MAXPOOL

The `TENS_MAXPOOL` transformation performs a maxpooling operation on an input tensor resulting in output tensor, based on stride, padding and kernel parameters. Channel_in must be divisible by SIMD vector width.

### YAML Specification

| FIELD      | TYPE  | EXAMPLE  | DESCRIPTION  |
|------------|-------|----------|--------------|
|tens_trans_type|string|TENS_MAXPOOL|Transformation identifier, shall be TENS_MAXPOOL in this case.|
|src_name|string|maxpool_tens|Input (input feature map) tensor name. Tensor shall have three dimensions: (height_in, width_in, channel_in). Tensor layout is column-first.|
|kern_size|list|[3, 2]|List of two integers. Sets the maxpooling kernel dimensions.|
|stride|list|[2, 3]|List of two integers. Sets the maxpooling stride parameters.|
|padding|list|[1, 2]|List of two integers. Sets the maxpooling padding parameters.|
|res_name|string|lin_out_tens|Name of the maxpooling output tensor. Has three dimensions: (height_out, width_out, channel_in). Tensor layout is column-first.|
|res_description|string|this is an maxpooling output tensor|optional comment|
|dealloc|list|[lin_in_tens, lin_weight_tens]|List of names of tensors to be deallocated after this operation.|



