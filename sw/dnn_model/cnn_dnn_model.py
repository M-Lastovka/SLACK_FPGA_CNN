import torch
import torch.nn as nn
import torch.optim as optim
import torch.nn.functional as F
import torchvision
import torchvision.transforms as transforms
import numpy as np
import random
import time

# Device configuration
device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
print(f'Available device:{device}')

# Hyperparameters
num_epochs = 10
learning_rate = 0.001
batch_size = 64
vect_size = 16

# CIFAR-10 dataset
transform = transforms.Compose(
    [transforms.RandomHorizontalFlip(),
     transforms.RandomCrop(32, padding=4),
     transforms.ToTensor(),
     transforms.Normalize((0.4914, 0.4822, 0.4465), (0.2023, 0.1994, 0.2010))])

train_dataset = torchvision.datasets.CIFAR10(root='./data', train=True, download=True, transform=transform)
test_dataset = torchvision.datasets.CIFAR10(root='./data', train=False, download=True, transform=transform)

train_loader = torch.utils.data.DataLoader(dataset=train_dataset, batch_size=batch_size, shuffle=True)
test_loader = torch.utils.data.DataLoader(dataset=test_dataset, batch_size=batch_size, shuffle=False)

def cust_image_flatten(tens, vect_size):
    assert tens.shape[0] % vect_size == 0 and len(tens.shape) == 3, "The number of channels must be divisible by vect_size, only 3D tensors are allowed"
    
    #empty list to hold the flattened slices
    flattened_slices = []
    
    #iterate over the slices and flatten
    for start in range(0, tens.shape[0], vect_size):
        slice = tens[start:start + vect_size, :, :]
        slice_perm = slice.permute(1, 2, 0)
        flattened_slice = torch.flatten(slice_perm)  
        flattened_slices.append(flattened_slice)
    
    # Concatenate all the flattened slices
    flattened_vector = torch.cat(flattened_slices, dim=0)
    
    return flattened_vector

def cust_flatten(tens, vect_size):

    #empty list to hold the flattened images
    flattened_images = []

    for i in range(tens.shape[0]):
        flattened_image = cust_image_flatten(tens[i, :, :, :], vect_size)
        flattened_images.append(flattened_image)
    
    flattened_batch = torch.stack(flattened_images)

    return flattened_batch

#Model definitions
class CIFAR_class_cnn_0(nn.Module):
    def __init__(self):
        super(CIFAR_class_cnn_0, self).__init__()

        self.conv_layer_0  = nn.Conv2d(3, 16, kernel_size=3, stride=2, padding=1)
        self.batch_layer_0 = nn.BatchNorm2d(16)
        self.pool_layer_0  = nn.MaxPool2d(kernel_size=3, stride=3)
        self.lin_layer_0   = nn.Linear(400, 16)
    
    def forward(self, x):
        out = self.conv_layer_0(x)
        out = self.batch_layer_0(out)
        out = F.relu(out)
        out = self.pool_layer_0(out)
        out = cust_flatten(out, vect_size)
        out = self.lin_layer_0(out)
        return out
    
class CIFAR_class_cnn_1(nn.Module):
    def __init__(self):
        super(CIFAR_class_cnn_1, self).__init__()

        self.conv_layer_0  = nn.Conv2d(3, 32, kernel_size=3, stride=1, padding=1)
        self.batch_layer_0 = nn.BatchNorm2d(32)
        self.pool_layer_0  = nn.MaxPool2d(kernel_size=2, stride=2)
        self.dropout_0     = nn.Dropout(0.25)
        self.conv_layer_1  = nn.Conv2d(32, 64, kernel_size=3, stride=1, padding=1)
        self.batch_layer_1 = nn.BatchNorm2d(64)
        self.pool_layer_1  = nn.MaxPool2d(kernel_size=2, stride=2)
        self.dropout_1     = nn.Dropout(0.25)
        self.conv_layer_2  = nn.Conv2d(64, 128, kernel_size=3, stride=1, padding=1)
        self.batch_layer_2 = nn.BatchNorm2d(128)
        self.pool_layer_2  = nn.MaxPool2d(kernel_size=2, stride=2)
        self.dropout_2     = nn.Dropout(0.25)
        self.lin_layer_0   = nn.Linear(2048, 512)
        self.batch_layer_3 = nn.BatchNorm1d(512)
        self.dropout_3     = nn.Dropout(0.5)
        self.lin_layer_1   = nn.Linear(512, 32)
    
    def forward(self, x):
        out = self.conv_layer_0(x)
        out = self.batch_layer_0(out)
        out = F.relu(out)
        out = self.pool_layer_0(out)
        out = self.dropout_0(out)
        out = self.conv_layer_1(out)
        out = self.batch_layer_1(out)
        out = F.relu(out)
        out = self.pool_layer_1(out)
        out = self.dropout_1(out)
        out = self.conv_layer_2(out)
        out = self.batch_layer_2(out)
        out = F.relu(out)
        out = self.pool_layer_2(out)
        out = self.dropout_2(out)
        out = cust_flatten(out, vect_size)
        out = self.lin_layer_0(out)
        out = self.batch_layer_3(out)
        out = self.dropout_3(out)
        out = self.lin_layer_1(out)
        return out
    
class fcn_class(nn.Module):
    def __init__(self):
        super(fcn_class, self).__init__()

        self.conv_layer_0  = nn.Conv2d(32, 32, kernel_size=3, stride=1, padding=1)
        self.batch_layer_0 = nn.BatchNorm2d(32)
        self.conv_layer_1  = nn.Conv2d(32, 32, kernel_size=3, stride=1, padding=1)
        self.batch_layer_1 = nn.BatchNorm2d(32)
        self.conv_layer_2  = nn.Conv2d(32, 32, kernel_size=3, stride=1, padding=1)
        self.batch_layer_2 = nn.BatchNorm2d(32)
        self.conv_layer_3  = nn.Conv2d(32, 32, kernel_size=3, stride=1, padding=1)
        self.batch_layer_3 = nn.BatchNorm2d(32)
        self.conv_layer_4  = nn.Conv2d(32, 32, kernel_size=3, stride=1, padding=1)
        self.batch_layer_4 = nn.BatchNorm2d(32)
        self.conv_layer_5  = nn.Conv2d(32, 32, kernel_size=3, stride=1, padding=1)
        self.batch_layer_5 = nn.BatchNorm2d(32)
        self.conv_layer_6  = nn.Conv2d(32, 32, kernel_size=3, stride=1, padding=1)
        self.batch_layer_6 = nn.BatchNorm2d(32)
        self.conv_layer_7  = nn.Conv2d(32, 32, kernel_size=3, stride=1, padding=1)
        self.batch_layer_7 = nn.BatchNorm2d(32)
    
    def forward(self, x):
        out = self.conv_layer_0(x)
        out = self.batch_layer_0(out)
        out = F.relu(out)
        out = self.conv_layer_1(out)
        out = self.batch_layer_1(out)
        out = F.relu(out)
        out = self.conv_layer_2(out)
        out = self.batch_layer_2(out)
        out = F.relu(out)
        out = self.conv_layer_3(out)
        out = self.batch_layer_3(out)
        out = F.relu(out)
        out = self.conv_layer_4(out)
        out = self.batch_layer_4(out)
        out = F.relu(out)
        out = self.conv_layer_5(out)
        out = self.batch_layer_5(out)
        out = F.relu(out)
        out = self.conv_layer_6(out)
        out = self.batch_layer_6(out)
        out = F.relu(out)
        out = self.conv_layer_7(out)
        out = self.batch_layer_7(out)
        out = F.tanh(out)
        return out

model = fcn_class().to(device)

# Loss and optimizer
criterion = nn.CrossEntropyLoss()
optimizer = optim.Adam(model.parameters(), lr=learning_rate)

# Training the model
def train_model():
    model.train()
    total_step = len(train_loader)
    for epoch in range(num_epochs):
        for i, (images, labels) in enumerate(train_loader):
            images = images.to(device)
            labels = labels.to(device)

            # Forward pass
            outputs = model(images)
            loss = criterion(outputs, labels)

            # Backward and optimize
            optimizer.zero_grad()
            loss.backward()
            optimizer.step()

            if (i+1) % 100 == 0:
                print(f'Epoch [{epoch+1}/{num_epochs}], Step [{i+1}/{total_step}], Loss: {loss.item():.4f}')

# Testing the model
def test_model():
    model.eval()
    with torch.no_grad():
        correct = 0
        total = 0
        for images, labels in test_loader:
            images = images.to(device)
            labels = labels.to(device)
            outputs = model(images)
            _, predicted = torch.max(outputs.data, 1)
            total += labels.size(0)
            correct += (predicted == labels).sum().item()

        print(f'Accuracy of the model on the test images: {100 * correct / total:.2f}%')

def adjust_dims(tens):
    ret_tens = None
    if(len(tens.shape) == 4):
        ret_tens = np.transpose(tens, (2, 3, 1, 0))
    elif(len(tens.shape) == 3):
        ret_tens = np.transpose(tens, (1, 2, 0))
    else:
        ret_tens = tens
    return ret_tens
        

def process_batch_norm_layer(name, module, params_np): # Function to process batch normalization layers
    # Merge the weight, bias, running mean, and running variance
    weight = module.weight.detach().numpy()
    bias = module.bias.detach().numpy()
    running_mean = module.running_mean.detach().numpy()
    running_var = module.running_var.detach().numpy()

    batch_scale  = weight / running_var
    batch_offset = (-weight * running_mean) / running_var + bias

    batch_joint = np.column_stack((batch_scale, batch_offset))

    # Store in the dictionary
    params_np[f'{name}'] = batch_joint

def gen_model_weight_csv(pth_file_name):
    model.load_state_dict(torch.load(pth_file_name))
    
    params_np = {}

    #go through all layers, convert to numpy, fuse batch norm
    for name, module in model.named_modules():
        if isinstance(module, nn.BatchNorm1d) or isinstance(module, nn.BatchNorm2d): #batch norm layers are fused
            process_batch_norm_layer(name, module, params_np)
        elif hasattr(module, 'weight') and module.weight is not None:
            weight = adjust_dims(module.weight.detach().numpy())
            params_np[f'{name}.weight'] = weight
            if module.bias is not None:
                bias = adjust_dims(module.bias.detach().numpy())
                params_np[f'{name}.bias'] = bias

    #print found weights
    print("Found following model weight tensors:")
    for key, value in params_np.items():
        print(f"{key}: {value.shape}")

    #save weights to a CSV file
    with open('../sim_scripts/cnn_weights.csv', 'w') as file:
        for key, value in params_np.items():
            flat_array = value.flatten()
            flat_array_str = ','.join(map(str, flat_array))
            file.write(f"{key},{flat_array_str}\n")

def gen_test_samples_csv(test_loader, test_samples_size=1):
    
    params_np = {}

    for i in range(test_samples_size):            
        #pick random sample from the first batch
        for batch_sample, _ in test_loader:
            test_sample = batch_sample[random.randint(0, test_loader.batch_size - 1)]
            break

        params_np[f'test_sample_{i}'] = test_sample.numpy()

    #save samples to a CSV file
    with open('../sim_scripts/cnn_test_samples.csv', 'w') as file:
        for key, value in params_np.items():
            flat_array = value.flatten()
            flat_array_str = ','.join(map(str, flat_array))
            file.write(f"{key},{flat_array_str}\n")

def test_model_latency(batch_size=1, num_iterations=50000, pre_warm_iterations=5000):     # Inference latency testing
    model.eval()
    input_shape = (32, 16, 32)  # Input shape (C, H, W)

    # Pre-warming period
    for _ in range(pre_warm_iterations):
        with torch.no_grad():
            input_data = torch.randn(batch_size, *input_shape)
            _ = model(input_data)

    # Measure latency
    latencies = []
    for _ in range(num_iterations):
        input_data = torch.randn(batch_size, *input_shape)
        start_time = time.time()
        with torch.no_grad():
            _ = model(input_data)
        end_time = time.time()
        latencies.append(end_time - start_time)

    # Compute average latency
    average_latency = sum(latencies) / num_iterations
    print(f"Average inference latency: {average_latency * 1e6:.8f} us")


# Run training and testing
if __name__ == '__main__':
    #gen_model_weight_csv('test_cnn_model.pth')
    #gen_test_samples_csv(test_loader, 2)
    test_model_latency()
    #train_model()
    #test_model()
    #torch.save(model.state_dict(), 'test_cnn_model.pth')