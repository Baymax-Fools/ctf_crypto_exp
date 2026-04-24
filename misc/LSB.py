#!/usr/bin/env python3
# 卷王杯 - 概率RSA
from pwn import *
from Crypto.Util.number import *
import re


p = remote('pwn.challenge.ctf.show', 28135)

# context.log_level = 'debug'
def oracle(c):
    l = []
    for i in range(20):
        p.sendline(str(c))
        s = p.recvuntil(b"temp_c = ")
        l.append(int(re.findall(b"\)\s*=\s*([0-9]*)", s)[0]))
    flag0 = 0
    flag2 = 0
    for i in range(20):
        if l[i] % 2 != 0:
            flag0 = 1
        if l[i] > 10000:
            flag2 = 1
    return [flag2, flag0]


def main():
    ss = p.recvuntil(b"temp_c = ")
    N = int(re.findall(b"N\s*=\s*(\d+)", ss)[0])
    e = int(re.findall(b"e\s*=\s*(\d+)", ss)[0])
    C = int(re.findall(b"c\s*=\s*(\d+)", ss)[0])
    print("N=", N)
    print("e=", e)
    print("c=", C)
    c = (pow(2, e, N) * C) % N
    LB = 0
    UB = N
    i = 1
    while LB != UB:
        flag = oracle(c)
        print(i, flag)
        if flag[1] % 2 == 0:
            UB = (LB + UB) // 2
        else:
            LB = (LB + UB) // 2
        c = (pow(2, e, N) * c) % N
        i += 1
    print(LB)
    print(UB)
    for i in range(-128, 128):
        temp = LB
        temp += i
        if pow(temp, e, N) == C:
            print(long_to_bytes(temp))
            exit(0)


if __name__ == '__main__':
    main()
    p.interactive()
