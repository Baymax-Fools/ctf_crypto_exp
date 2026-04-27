#!/usr/bin/env python3
from pwn import *
import binascii

p = remote('59.110.158.148', 26720)

p.recvuntil(b"Tag: ")
token = p.recvline().strip().decode()

# p.sendlineafter(b"> ", b"1")  
# p.sendlineafter(b"Hex: ", token_hex.encode())

x = binascii.unhexlify(token)
iv = x[:16]
c0 = x[16:32]
c1 = x[32:]
print(len(x))
print(len(iv))
print(len(c0))
print(len(c1))

def check(pay):
    p.sendlineafter(b"> ", b"1")
    p.sendlineafter(b"Hex: ", pay.encode())
    res = p.recvuntil([b"(x_x)", b"(o_O)", b"(^v^)"])
    return b"(x_x)" not in res

def decode(target_block, prev_block):
    I = bytearray(16)
    P = bytearray(16)
    
    for i in range(1, 17):
        padding = i
        prefix = bytearray(16 - i)
        suffix = bytearray([I[j] ^ padding for j in range(16-i+1, 16)])
        
        for b in range(256):
            test_iv = prefix + bytearray([b]) + suffix

            che = check(binascii.hexlify(test_iv + target_block).decode())
            if che:
                I[16-i] = b ^ padding
                P[16-i] = I[16-i] ^ prev_block[16-i]
                print(P)
                break
    return P

p2 = decode(c1, c0)
p1 = decode(c0, iv)

seed = (p1 + p2).strip()
p.sendlineafter(b"> ", b"2")
p.sendlineafter(b"Seed: ", seed)
p.interactive()
