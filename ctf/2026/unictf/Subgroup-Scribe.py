#!/usr/bin/env python3
from pwn import *
from os import urandom

sbox = [147, 138, 104,  87,   5, 201, 249, 141, 243,  72,  71, 221,  97, 174,  48, 155,
        114, 225, 117, 105, 224,  70,   7, 108, 190, 146, 145, 130,  46, 209, 229, 226,
         15, 112, 103,  27,  91, 181, 253, 183, 152, 165, 110,  44, 160,  66, 116,   0,
         75,  26,  61,  96, 127, 157, 197, 164, 172,  20,  37,  68, 202, 101,   9,   3,
        109,  31, 208,  98,  11, 144,  79,  25, 239, 231,  43,  36,  10,   2, 170, 251,
        161, 135, 134, 166, 136, 177, 215,  82, 244, 218,  47, 137, 242,  76, 233, 115,
        182, 153, 214,  84,  13, 159,  60,  74,  65,  54, 163,  56, 180,  30, 139, 236,
         67,  64,  80, 119,  40, 206, 148,  93, 217,  81, 126, 162, 185, 186,  77, 234,
         45, 142, 230, 179,  34, 193, 124, 107, 125, 198,  90,  23,  12, 232, 100,  16,
        120,  59,   1,   6, 102,  24, 133, 176, 150, 187,  28,  51, 195,  85, 196, 219,
        167, 227,  38,  55, 248, 241, 204, 235, 192, 194,  52, 252, 247,   4, 212,  58,
         78, 245, 240,  21,  14,  29, 169,   8, 121,  86, 118, 184, 143, 129,  69, 205,
        132, 213, 246, 238,  73,  53, 122,  62,  35, 210, 250, 149,  17, 203, 111,  18,
        158,  33, 151,  50,  83,  57,  92, 123,  95,  63, 216, 189, 173, 175, 220,  94,
        106,  41, 222, 154,  89, 156, 171,  32, 200,  88, 254,  99, 140, 228, 188, 207,
         19, 113, 255,  49, 237, 223, 191, 168,  42, 211,  22, 199, 128,  39, 178, 131]

def rotl(x, n):
    return ((x << n) & 0xFFFFFFFF) | (x >> (32 - n))

def tau(a):
    return ((sbox[(a >> 24) & 0xFF] << 24) |
            (sbox[(a >> 16) & 0xFF] << 16) |
            (sbox[(a >> 8) & 0xFF] << 8) |
             sbox[a & 0xFF])

def L(b):
    return b ^ rotl(b, 2) ^ rotl(b, 10) ^ rotl(b, 18) ^ rotl(b, 24)

possible_T1 = set()
for i in range(256):
    # 因为 X 和 X^1 只有最低位字节不同，所以 tau 之后的异或差值只存在于最低字节
    diff_tau = sbox[i] ^ sbox[i ^ 1]
    # L 函数是线性的，所以 T(X) ^ T(X^1) = L(tau(X) ^ tau(X^1))
    possible_T1.add(L(diff_tau))

p = remote("nc1.ctfplus.cn", 37539)
# context(log_level='debug')
for i in range(128):
    msg = [b'\x00' * 16] 
    
    for _ in range(127):
        msg.append(urandom(16))
        
    # 第 129 个块：[1, 1, 1, 0]
    msg.append(b'\x00\x00\x00\x01' * 3 + b'\x00\x00\x00\x00')

    msg_hex = b''.join(msg).hex()

    p.recvuntil(b'msg > ')
    p.sendline(msg_hex.encode())

    p.recvuntil(b'hint: ')
    hint = bytes.fromhex(p.recvline()[:-1].decode())

    # 分析hint并猜测coin 
    # 如果是密文（129个块）
    # 提取第1个块（全0）和第129个块（[1,1,1,0]）的密文
    enc_A = hint[0:16]  # 第1个块的密文
    enc_B = hint[128*16:129*16]  # 第129个块的密文
    
    # 提取第四个32位字（最后4个字节）
    word_A = int.from_bytes(enc_A[12:16], 'big')
    word_B = int.from_bytes(enc_B[12:16], 'big')
    diff = word_A ^ word_B
    
    # 判断 diff 是否在可能的差分值中
    if diff in possible_T1:
        coin = 0  # hint是密文
    else:
        coin = 1  # hint是随机数

    print(f'Guessing coin = {coin}')
    p.sendline(str(coin).encode())

p.interactive()

'''
from os import urandom
from random import randint
from secret import flag

sbox = [147, 138, 104,  87,   5, 201, 249, 141, 243,  72,  71, 221,  97, 174,  48, 155,
        114, 225, 117, 105, 224,  70,   7, 108, 190, 146, 145, 130,  46, 209, 229, 226,
         15, 112, 103,  27,  91, 181, 253, 183, 152, 165, 110,  44, 160,  66, 116,   0,
         75,  26,  61,  96, 127, 157, 197, 164, 172,  20,  37,  68, 202, 101,   9,   3,
        109,  31, 208,  98,  11, 144,  79,  25, 239, 231,  43,  36,  10,   2, 170, 251,
        161, 135, 134, 166, 136, 177, 215,  82, 244, 218,  47, 137, 242,  76, 233, 115,
        182, 153, 214,  84,  13, 159,  60,  74,  65,  54, 163,  56, 180,  30, 139, 236,
         67,  64,  80, 119,  40, 206, 148,  93, 217,  81, 126, 162, 185, 186,  77, 234,
         45, 142, 230, 179,  34, 193, 124, 107, 125, 198,  90,  23,  12, 232, 100,  16,
        120,  59,   1,   6, 102,  24, 133, 176, 150, 187,  28,  51, 195,  85, 196, 219,
        167, 227,  38,  55, 248, 241, 204, 235, 192, 194,  52, 252, 247,   4, 212,  58,
         78, 245, 240,  21,  14,  29, 169,   8, 121,  86, 118, 184, 143, 129,  69, 205,
        132, 213, 246, 238,  73,  53, 122,  62,  35, 210, 250, 149,  17, 203, 111,  18,
        158,  33, 151,  50,  83,  57,  92, 123,  95,  63, 216, 189, 173, 175, 220,  94,
        106,  41, 222, 154,  89, 156, 171,  32, 200,  88, 254,  99, 140, 228, 188, 207,
         19, 113, 255,  49, 237, 223, 191, 168,  42, 211,  22, 199, 128,  39, 178, 131]


FK = [0xA3B1BAC6, 0x56AA3350, 0x677D9197, 0xB27022DC]
CK = [0x00070E15, 0x8C939AA1, 0x181F262D, 0xA4ABB2B9, 0xAC019832, 0XD8DFE6ED, 0X2C333A41]


def rotl(x, n):
    return ((x << n) & 0xFFFFFFFF) | (x >> (32 - n))

def tau(a):
    return ((sbox[(a >> 24) & 0xFF] << 24) |
            (sbox[(a >> 16) & 0xFF] << 16) |
            (sbox[(a >> 8) & 0xFF] << 8) |
             sbox[a & 0xFF])

def L(b):
    return b ^ rotl(b, 2) ^ rotl(b, 10) ^ rotl(b, 18) ^ rotl(b, 24)

def T(x):
    return L(tau(x))

def T_prime(x):
    b = tau(x)
    return b ^ rotl(b, 13) ^ rotl(b, 23)

def gen_key(mk_int):
    k = [(mk_int >> 96) & 0xFFFFFFFF, (mk_int >> 64) & 0xFFFFFFFF, 
         (mk_int >> 32) & 0xFFFFFFFF, mk_int & 0xFFFFFFFF]
    k = [k[0] ^ FK[0], k[1] ^ FK[1], k[2] ^ FK[2], k[3] ^ FK[3]]
    rk = []
    for i in range(7):
        k_next = k[i] ^ T_prime(k[i+1] ^ k[i+2] ^ k[i+3] ^ CK[i])
        k.append(k_next)
        rk.append(k_next)
    return rk

def encrypt(msg, key):
    assert len(msg) == len(key) == 16

    msg = int.from_bytes(msg)
    key = int.from_bytes(key)
    rk = gen_key(key)
    x = [(msg >> 96) & 0xFFFFFFFF, (msg >> 64) & 0xFFFFFFFF, 
         (msg >> 32) & 0xFFFFFFFF, msg & 0xFFFFFFFF]
    
    for i in range(7):
        x_next = x[0] ^ T(x[1] ^ x[2] ^ x[3] ^ rk[i])
        x = x[1:] + [x_next]
    
    y = x[::-1]
    return int.to_bytes((y[0] << 96) | (y[1] << 64) | (y[2] << 32) | y[3], 16)

def enc_ecb(msg, key):
    assert len(msg) % 16 == len(key) % 16 == 0
    msg = [msg[16 * i : 16 * i + 16] for i in range(len(msg) // 16)]
    enc = []
    for i in msg:
        enc += [encrypt(i, key)]
        key = bytes([sbox[i] for i in key]) # 
    return b''.join(enc)

ROUNDS = 128
for r in range(ROUNDS):
    print(f"--- Round {r + 1}/{ROUNDS} ---")
    key = urandom(16)
    coin = randint(0, 1)
    msg = bytes.fromhex(input('msg > '))
    if len({*zip(*[iter(msg)] * 16)}) * 16 != len(msg): print('🤡'); exit()
    enc = enc_ecb(msg, key)
    print(f'hint: {[enc.hex(), urandom(len(enc)).hex()][coin]}')
    if int(input('give me coin > ')) != coin: print('🤬'); exit()
print(f'😊: {flag}')

'''