import libnum

a = 0x2559659965656A9A65656996696965A6695669A9695A699569666A5A6A6569666A59695A69AA696569666AA6
b = bin(a)[2:]
flag = ''
for i in range(0, len(b), 2):
    if b[i:i + 2] == '10':
        flag = flag + '1'
    else:
        flag = flag + '0'
print(flag)
ans = int(flag, 2)
print(libnum.n2s(ans))