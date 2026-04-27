#!/usr/bin/env python3
from sage.all import *
from Crypto.Util.number import *
from pwn import *

io = remote("cloud-big.hgame.vidar.club",30615)
context(log_level='debug')

p = int(io.recvline().decode().strip())
print(f'p=',p)

a = int(io.recvline().decode().strip())
b = int(io.recvline().decode().strip())
R = io.recvuntil(b' : 1)').decode().strip()
R_x = int(R.replace('(', '').replace(')', '').replace(' ', '').split(":")[0])
R_y = int(R.replace('(', '').replace(')', '').replace(' ', '').split(":")[1])
print(f'R=',R)
print(f'R_x',R_x)
print(f'R_y',R_y)

def recv_data(t):
    io.recvuntil(b'>')
    io.sendline(b'1')
    io.recvuntil(b't> t = ')
    io.sendline(str(t).encode())
    return int(io.recvline().decode().strip())

hs = []
h_0 = recv_data(0)
hs.append(h_0)
for i in range(1,15):
    h_i = recv_data(i)
    h_inv_i = recv_data(-i)
    hs.append(h_i + h_inv_i)

assert len(hs) == 15

p = p
a = a
b = b
E = EllipticCurve(GF(p), [a, b])
G = E((R_x, R_y))
hs = hs
k = 163
d = len(hs) - 1
Ai = []
A0i = []
Bi = []
B0i = []
Ci = []
for i in range(1, d + 1):
    Q = i * G
    xQ = ZZ(Q[0])
    Ai.append(hs[i] - 2 * xQ)
    A0i.append(2 * (hs[0] - xQ))
    Bi.append(2 * (hs[i] * (hs[0] - xQ) - 2 * hs[0] * xQ - a - xQ ** 2))
    B0i.append((hs[0] - xQ) ** 2)
    Ci.append(hs[i] * (hs[0] - xQ) ** 2 - 2 * ((hs[0] ** 2 +a) * xQ + (a + xQ ** 2) * hs[0] + 2 * b))
R = block_matrix(ZZ, [-matrix(Ci), -matrix(Bi), -diagonal_matrix(B0i), -matrix(Ai), -diagonal_matrix(A0i)], ncols=1)
P = diagonal_matrix(ZZ, [p] * d)
E = block_diagonal_matrix([matrix([8**k]), diagonal_matrix([4**k] * (d + 1)), diagonal_matrix([2**k] * (d + 1))])

Z = zero_matrix(ZZ, P.nrows(), E.ncols())
M = block_matrix([[E, R], [Z, P]])
shortest_vector = M.LLL()[0]
es = shortest_vector[1:d+1] / 4 ** k
xP = ZZ(hs[0] + es[0])
print(f"xP=",xP)

io.recvline(b'> \n')
io.sendline(b'2')
sleep(2)
io.sendline(str(xP).encode())

io.interactive()