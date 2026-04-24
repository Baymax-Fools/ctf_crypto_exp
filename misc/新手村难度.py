#!/usr/bin/env python3
# 新手杯 - 新手村难度

import random
import tqdm
from pwn import *
from Crypto.Util.number import *

re = remote('pwn.challenge.ctf.show', 28216)
re.recvuntil(b'p = ')
p = int(re.recvline().decode()[:-1])
if p % 4 != 3:
    re.close()
    exit()
re.recvuntil(b'len(flag) = ')
flag_len = int(re.recvline().decode()[:-1])
print(p, flag_len)
flag = [-1 for i in range(flag_len)]
INDEX = []
SEED = []
seed = 0
while len(SEED) != flag_len:
    random.seed(seed)
    randlist = list(range(flag_len))
    random.shuffle(randlist)
    indexx = list(range(flag_len)).index(randlist[0])
    if indexx not in INDEX:
        INDEX.append(indexx)
        SEED.append(seed)
    seed += 1
assert len(SEED) == flag_len
for i in tqdm.tqdm(range(len(SEED))):
    re.recvuntil(b'> ')
    re.sendline(str(SEED[i]).encode())
    re.recvuntil(b'newbie(sometimes_naive, p) = ')
    c = int(re.recvline().decode()[:-1])
    check = pow(c, (p - 1) // 2, p)
    flag[INDEX[i]] = 0 if check == 1 else 1
flag = [str(i) for i in flag]
print(long_to_bytes(int(''.join(flag), 2)))

re.close()

