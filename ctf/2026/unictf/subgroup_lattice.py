#!/usr/bin/env python3
from pwn import *
from sage.all import *
from tqdm import *
import cuso
from Crypto.Util.number import *

m = 2147483647
n = 16
alpha = 17
beta = 14
K = 2**beta     

r = 71
t = 71
N = 141

io = remote('nc1.ctfplus.cn',14097)

hints = []
for _ in trange(N):
    io.sendlineafter(b'>>> ', b'2')
    io.recvuntil(b'hint: ')
    tmp = int(io.recvline().strip())
    hints.append(tmp)

L = Matrix(ZZ, t + r, t + r)

for i in range(t):
    L[i, i] = m

for i in range(r):
    Y = hints[i : i + t]
    for j in range(t):
        L[t + i, j] = K * Y[j]
    L[t + i, t + i] = K

res = L.BKZ(block_size=30)
R = GF(m)['x']
candidates = []

for v in res:
    if v.norm() == 0: 
        continue

    coeffs = []
    is_valid = True
    for k in range(r):
        coeffs.append(v[t + k] // K)
    
    if is_valid:
        try:
            poly = R(coeffs)
            d = poly.degree()
            if d >= n:
                candidates.append(poly)
        except:
            pass
    
    if len(candidates) >= 10: 
        break

F = candidates[0]
for p in candidates[1:]:
    tmp = gcd(F, p)
    if tmp.degree() >= n:
        F = tmp

F = F.monic()
# print(F)

assert F.is_primitive() and F.degree() == n

C = [int(c) for c in (-F).coefficients(sparse=False)[:-1]]

l = [var(f'l{i}') for i in range(2*n)]

xs = [2**14 * hints[i] + l[i] for i in range(2*n)]
relations = []

for i in range(n):
    f = 0
    for j in range(n):
        f += C[j] * xs[i + j]
    f -= xs[i + n]
    relations.append(f)

bounds = {l[i]: (0, 2**14) for i in range(2*n)}

sols = cuso.find_small_roots(relations, bounds=bounds, modulus=m)

state = [2**14 * hints[i] + sols[0][l[i]] for i in range(n)]

for i in range(n):
    tmp = state[-1]
    for j in range(n-1):
        tmp = (tmp - C[j+1] * state[j]) % m
    
    tmp = tmp * inverse(C[0], m) % m
    state = [tmp] + state[:-1]

ans = sum(state)
io.sendlineafter(b'>>> ', b'1')
io.sendlineafter(b'Please enter the answer: ', str(ans).encode())

io.interactive()
