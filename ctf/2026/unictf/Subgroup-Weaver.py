#!/usr/bin/env python3
from pwn import *

p = remote("nc1.ctfplus.cn",17075)

re_list = []

for i in range(2500):
    p.sendlineafter(b'>',b'1')
    x = p.recvline().strip()
    re_list.append(int(x))
    if i % 100 == 0:
        print(i)

k_bit = []
key = 0

for i in range(512):
    k1 = 0
    for j in re_list:
        k1 += (j>>i) & 1
    if k1 > (2500 // 2):
        k_bit.append(0)
    else:
        k_bit.append(1)
    if i % 100 == 0:
        print(i)

j = 0
for i in k_bit:
    key += (i << j)
    j += 1

print(key)
k_hex = hex(key)[2:].rjust(128, '0')
print(k_hex)

p.sendline(k_hex.encode())
print(p.recv())


p.interactive()