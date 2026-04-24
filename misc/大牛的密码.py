from RSA.RSA_共模攻击 import result

S_BOX = [9, 31, 32, 38, 20, 1, 22, 4, 8, 2, 11, 21, 7, 18, 46, 23, 34, 3, 19, 12, 45, 30, 27, 37, 5, 47, 28, 36, 0, 43, 39, 10, 29, 14, 40, 24, 33, 16, 17, 6, 42, 15, 26, 41, 44, 25, 35, 13]
# 48 字节，flag的字节数为（36，47） s_box已经打乱了
c = [99, 111, 102, 11, 107, 49, 11, 53, 121, 48, 114, 117, 11, 95, 112, 95, 109, 115, 11, 95, 101, 95, 119, 117, 79, 123, 111, 48, 110, 95, 121, 116, 121, 125, 116, 11, 119, 11, 97, 67, 11, 11, 11, 11, 11, 99, 110, 104]
BLOCK = 16
#print(len(c))
#print(len(S_BOX))
#for j in range(16):  # BLOCK = 16
    #aa = j * 7 % 16
    #print(aa)

def find_inverse_sbox(S_BOX):
    in_sbox = [0] * len(S_BOX)
    for i, val in enumerate(S_BOX):
        in_sbox[val] = i
    return in_sbox

def decrypt2(encrypted):
    # 先找到逆S盒
    INV_S_BOX = find_inverse_sbox(S_BOX)

    # 逆向执行16轮
    m = encrypted
    for i in range(16):
        m = [m[i] for i in INV_S_BOX]
    return m

c1 = decrypt2(c)
# print(c1)

def swap(a,b):
    tmp = a
    a = b
    b = tmp

def decrypt1(m):
    enc=[m[i:i+BLOCK] for i in range(0,len(m),BLOCK)]
    for i in enc:
        for j in range(15,-1,-1):
            aa = j*7%BLOCK
            i[j],i[aa] = i[aa],i[j]
    result = []
    for i in enc:
        result += i
    return result

c2 = decrypt1(c1)
print(c2)

flag_bytes = bytes(c2)
print("Flag bytes:", flag_bytes)
print("Flag:", flag_bytes.decode('latin-1'))