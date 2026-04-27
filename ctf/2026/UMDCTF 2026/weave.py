import json
import hashlib
from Crypto.Cipher import AES

with open(r'F:\download\CTF\output.json', 'r') as fh:
    handout = json.load(fh)

spec = handout['spec']
Q = spec['q']
M = spec['m']
N = spec['n']
K = spec['k']
FRAYS = spec['frays']
modulus_coeffs = spec['modulus']

P.<x> = PolynomialRing(GF(Q))
MODPOLY = P(modulus_coeffs)
Fq = GF(Q)
Fqm.<a> = GF(Q**M, modulus=MODPOLY, name='a')

def unpack(data):
    elements = []
    for val in data:
        coeffs = [Fq((val >> i) & 1) for i in range(M)]
        elements.append(Fqm(P(coeffs)))
    return vector(Fqm, elements)

def unpack_mat(data):
    rows = [unpack(row) for row in data]
    return Matrix(Fqm, rows)

warp = unpack_mat(handout['warp'])
bolt = unpack(handout['bolt'])

loom_data = handout['loom']
pegs = list(unpack(loom_data['pegs']))
knot = unpack_mat(loom_data['knot'])
shuttle = unpack_mat(loom_data['shuttle'])
fibers = list(unpack(loom_data['fibers']))
FIBER_D = len(fibers)

vault = handout['vault']
iv = bytes.fromhex(vault['iv'])
body = bytes.fromhex(vault['body'])
tag = bytes.fromhex(vault['tag'])

# 1. 转换到 B' = S * loom + E
B_prime = bolt * shuttle

# 2. 构造 Welch-Berlekamp 线性方程组
# W(x) 阶数 = (K - 1) + 15 = 22 (23 个未知数 w_0 ... w_22)
# Lambda(x) 阶数 = 15 (假设 lambda_0 = 1, 有 15 个未知数 lambda_1 ... lambda_15)
# 总共 38 个未知数，利用 N=40 个点进行评估，必然有唯一解
mat_rows = []
vec_rhs = []

for i in range(N):
    row = []
    # 填充 W(x) 的系数项 w_j
    for j in range(23):
        row.append(pegs[i] ** (2**j))
    # 填充 Lambda(x) 的系数项 lambda_k (由于在GF(2)上减法等于加法，直接用加法)
    for k in range(1, 16):
        row.append( B_prime[i] ** (2**k) )
    
    mat_rows.append(row)
    # 等式右边为 lambda_0 * B'_i，由于我们设 lambda_0 = 1，所以常数项就是 B'_i
    vec_rhs.append(B_prime[i])

Mat = Matrix(Fqm, mat_rows)
Vec = vector(Fqm, vec_rhs)

X = Mat.solve_right(Vec)

W_coeffs = list(X[:23])
Lambda_coeffs = [Fqm(1)] + list(X[23:])

# 3. 递归求解 L(x) 的系数 S_0 ... S_7
# 由关系式 W(x) = Lambda(L(x)) 可知可以由低到高逐级求出 S 的各项系数
S = []
for m in range(8):
    sm = W_coeffs[m]
    for k in range(1, m + 1):
        sm -= Lambda_coeffs[k] * (S[m - k] ** (2**k))
    S.append(sm)

# 4. 恢复真正的 secret 向量
S_vec = vector(Fqm, S)
secret = S_vec * knot.inverse()

# 5. 打包并计算 AES Key 进行解密
def pack(v):
    out = []
    for e in v:
        cs = list(e.polynomial()) if e else []
        cs = [int(c) for c in cs] + [0] * (M - len(cs))
        val = 0
        for i, c in enumerate(cs):
            val |= c << i
        out.append(int(val))
    return out

secret_packed = pack(secret)
secret_bytes = b''.join(int(v).to_bytes((M + 7) // 8, 'big') for v in secret_packed)
wrap_key = hashlib.sha256(secret_bytes).digest()[:16]

cipher = AES.new(wrap_key, AES.MODE_GCM, nonce=iv)

m = cipher.decrypt_and_verify(body, tag)
print(m)

"""
#!/usr/bin/env sage
import json, os
from hashlib import sha256
from Crypto.Cipher import AES

Q       = 2
M       = 43
N       = 40
K       = 8
FRAYS   = 5
FIBER_D = 3

R.<x> = PolynomialRing(GF(Q))
MODPOLY = x**43 + x**21 + x**3 + x + 1
assert MODPOLY.is_irreducible()

Fq      = GF(Q)
Fqm.<a> = GF(Q**M, modulus=MODPOLY) # 2的43次扩域

set_random_seed(int.from_bytes(os.urandom(32), 'big'))

def qpow(e, j):
    return e ** (Q ** j)    # 幂塔

def pick_independent(count):    # 在有限域扩张上生成随机线性无关组
    while True:
        vs = [Fqm.random_element() for _ in range(count)]
        rows = []
        for v in vs:
            cs = list(v.polynomial()) if v else []
            cs = [Fq(c) for c in cs] + [Fq(0)] * (M - len(cs))
            rows.append(cs)
        if Matrix(Fq, rows).rank() == count:    # 满秩
            return vs

def pick_invertible_Fqm(sz):
    while True:
        M_ = Matrix(Fqm, sz, sz, [Fqm.random_element() for _ in range(sz * sz)])
        if M_.is_invertible():
            return M_

def pick_shuttle(sz, fibers):
    while True:
        entries = []
        for _ in range(sz * sz):
            cs = [Fq.random_element() for _ in range(FIBER_D)]
            entries.append(sum(c * v for c, v in zip(cs, fibers)))
        M_ = Matrix(Fqm, sz, sz, entries)
        if M_.is_invertible():
            return M_

pegs    = pick_independent(N)
loom    = Matrix(Fqm, K, N, lambda j, i: qpow(pegs[i], j))
knot    = pick_invertible_Fqm(K)
fibers  = pick_independent(FIBER_D)
shuttle = pick_shuttle(N, fibers)
warp    = knot * loom * shuttle.inverse()

secret = vector(Fqm, [Fqm.random_element() for _ in range(K)])

def pack(v):
    out = []
    for e in v:
        cs = list(e.polynomial()) if e else []
        cs = [int(c) for c in cs] + [0] * (M - len(cs))
        val = 0
        for i, c in enumerate(cs):
            val |= c << i
        out.append(int(val))
    return out

def pack_mat(M_):
    return [pack(row) for row in M_.rows()]

secret_bytes = b''.join(int(v).to_bytes((M + 7) // 8, 'big') for v in pack(secret))
wrap_key = sha256(secret_bytes).digest()[:16]

try:
    flag = open('flag.txt', 'rb').read().strip()
except FileNotFoundError:
    flag = b'UMDCTF{test_flag}'

iv = os.urandom(12)
body, tag = AES.new(wrap_key, AES.MODE_GCM, nonce=iv).encrypt_and_digest(flag)

def pick_frays():
    while True:
        B = Matrix(Fq, 5, 40, [Fq.random_element() for _ in range(5 * 40)])
        if B.rank() == 5:
            break
    u = vector(Fqm, [Fqm.random_element() for _ in range(5)])
    return u * B.change_ring(Fqm)

frays = pick_frays()
bolt  = secret * warp + frays

handout = {
    'spec': {
        'q': int(Q),
        'm': int(M),
        'n': int(N),
        'k': int(K),
        'frays': int(FRAYS),
        'modulus': [int(c) for c in MODPOLY.list()],
    },
    'warp': pack_mat(warp),
    'bolt': pack(bolt),
    'loom': {
        'pegs':    pack(vector(Fqm, pegs)),
        'knot':    pack_mat(knot),
        'shuttle': pack_mat(shuttle),
        'fibers':  pack(vector(Fqm, fibers)),
    },
    'vault': {
        'iv':   iv.hex(),
        'body': body.hex(),
        'tag':  tag.hex(),
    },
}

with open('output.json', 'w') as fh:
    json.dump(handout, fh)

print('Output.json is created!')

"""