#!/usr/bin/env python3
from pwn import *
from sympy.ntheory.modular import crt
from Crypto.Util.number import long_to_bytes

io = remote("172.30.144.1", 64673)

mod = []
rem = []

for i in range(2, 257):
    io.recvuntil(b"Give me a base:")
    io.sendline(str(i).encode())
    io.recvuntil(b"Here you go: ")
    line = io.recvline()
    S = int(line)
    print(S)
    m = i - 1
    r = S % m

    mod.append(m)
    rem.append(r)

m = crt(mod, rem)[0]
print(long_to_bytes(m))

io.interactive()


