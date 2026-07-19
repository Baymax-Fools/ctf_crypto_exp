#!/usr/bin/env python3
from sage.all import *
from pwn import *
from ast import literal_eval
import hashlib
import random

n = 64
q = 65537
k = 2
l = 2
eta = 2
tau = 20
gamma1 = 8192
gamma2 = 256
beta = tau * eta
NOISE_BOUND = 15
TARGET_MSG = "Please give me the flag"

P = PolynomialRing(GF(q), 'x')
x = P.gen()
R = P.quotient(x**n + 1, 'x')

p = remote('isv1btq3-wiwe-jswc-cmz2-6a5c740c31714-neptune.nepctf.com', 443, ssl=True)

def high_bits(r, gamma2):
    r = int(r) % q
    r0 = r % gamma2
    if r0 > gamma2 // 2:
        r0 -= gamma2
    return (r - r0) // gamma2

def poly_high_bits(poly_coeffs, gamma2):
    return [high_bits(c, gamma2) for c in poly_coeffs]

def serialize_w1(w1_list):
    data = b""
    for coeffs in w1_list:
        for v in coeffs:
            data += int(v).to_bytes(2, "big")
    return data

def generate_challenge(msg, w1_list):
    data = msg.encode() + serialize_w1(w1_list)
    seed = hashlib.sha256(data).digest()
    rng = random.Random(seed)
    c_coeffs = [0] * n
    positions = rng.sample(range(n), tau)
    for pos in positions:
        c_coeffs[pos] = 1 if rng.randint(0, 1) == 0 else -1
    return c_coeffs  # centered: {-1, 0, 1}

def get_pkey():
    p.recvuntil(b'> ')
    p.sendline(b'1')
    p.recvuntil(b'A:')
    p.recvline()
    A11 = literal_eval(p.recvline().decode().strip())
    A12 = literal_eval(p.recvline().decode().strip())
    A21 = literal_eval(p.recvline().decode().strip())
    A22 = literal_eval(p.recvline().decode().strip())
    p.recvuntil(b't:')
    p.recvline()
    t1 = literal_eval(p.recvline().decode().strip())
    t2 = literal_eval(p.recvline().decode().strip())
    A = [[R(A11), R(A12)], [R(A21), R(A22)]]
    t = [R(t1), R(t2)]
    return A, t

def get_signature(msg):
    p.recvuntil(b'> ')
    p.sendline(b'2')
    p.recvuntil(b'Message to sign:')
    p.sendline(msg.encode())
    p.recvuntil(b'c:')
    c_raw = literal_eval(p.recvline().decode().strip())
    c_centered = [x if x <= q//2 else x - q for x in c_raw]
    p.recvuntil(b'z:')
    p.recvline()
    z0 = literal_eval(p.recvline().decode().strip())
    z1 = literal_eval(p.recvline().decode().strip())
    p.recvuntil(b'r (debug):')
    p.recvline()
    r0 = literal_eval(p.recvline().decode().strip())
    r1 = literal_eval(p.recvline().decode().strip())
    return c_centered, [z0, z1], [r0, r1]

def build_mult_matrix(c_centered):
    """
    Returns 64x64 matrix M over ZZ such that:
        M * s_coeffs = (c * s)_coeffs   (centered, as integers)
    """
    c_poly = R(c_centered)
    cols = []
    for k in range(n):
        e_k = [0] * n
        e_k[k] = 1
        result = c_poly * R(e_k)
        result_list = result.lift().coefficients(sparse=False)
        result_list = result_list + [0] * (n - len(result_list))
        result_centered = [int(v) if int(v) <= q//2 else int(v) - q for v in result_list]
        cols.append(result_centered)
    M = matrix(ZZ, cols).transpose()
    return M

def forge_signature(msg, A, t, s1_coeffs):
    while True:
        y = []
        for _ in range(l):
            coeffs = [random.randint(-8000, 8000) for _ in range(n)]
            y.append(coeffs)

        w = []
        for i in range(k):
            w_poly = R(0)
            for j in range(l):
                w_poly += A[i][j] * R(y[j])
            w_coeffs = w_poly.lift().coefficients(sparse=False)
            w_coeffs = w_coeffs + [0] * (n - len(w_coeffs))
            w.append([int(c) for c in w_coeffs])

        w1_list = [poly_high_bits(w[i], gamma2) for i in range(k)]
        c_centered = generate_challenge(msg, w1_list)
        c_poly = R(c_centered)

        z = []
        for j in range(l):
            s1_poly = R(s1_coeffs[j])
            z_poly = R(y[j]) + c_poly * s1_poly
            z_coeffs = z_poly.lift().coefficients(sparse=False)
            z_coeffs = z_coeffs + [0] * (n - len(z_coeffs))
            z_centered = [int(c) if int(c) <= q//2 else int(c) - q for c in z_coeffs]
            z.append(z_centered)

        z_all = [coeff for poly in z for coeff in poly]
        if max(abs(v) for v in z_all) < gamma1 - beta:
            c_submit = [x % q for x in c_centered]
            return c_submit, z

def recover_s1(c_list, d_list):
    """
    Given list of challenge vectors c and observations d = c*s - noise,
    recover s via accumulated least squares.
    """
    MTM = matrix(QQ, n, n, 0)
    MTd = vector(QQ, [QQ(0)] * n)

    for i in range(len(c_list)):
        M = build_mult_matrix(c_list[i])
        M_QQ = M.change_ring(QQ)
        d = vector(QQ, [QQ(v) for v in d_list[i]])
        MTM += M_QQ.T * M_QQ
        MTd += M_QQ.T * d

    # Regularization
    MTM_reg = MTM + matrix.identity(QQ, n) * QQ(1)/QQ(1000)

    try:
        s1_rec = MTM_reg.solve_right(MTd)
    except Exception:
        s1_rec = MTM_reg.pseudoinverse() * MTd

    s1_int = [round(QQ(x)) for x in s1_rec]
    s1_int = [max(-eta, min(eta, x)) for x in s1_int]
    return s1_int

A, t = get_pkey()

NUM_SIGS = 50

c_list = []
d0_list = []
d1_list = []

for i in range(NUM_SIGS):
    msg = f"test_{i}"
    c, z, r = get_signature(msg)
    d0 = [z[0][j] - r[0][j] for j in range(n)]
    d1 = [z[1][j] - r[1][j] for j in range(n)]
    c_list.append(c)
    d0_list.append(d0)
    d1_list.append(d1)
    if (i + 1) % 10 == 0:
        print(i+1)

print(f"  d0[0][:10] = {d0_list[0][:10]}")
print(f"  d0[0] min/max = {min(d0_list[0])} / {max(d0_list[0])}")

# Recover s1
s1_recovered = []
for idx, d_list in enumerate([d0_list, d1_list]):
    print(f"[*] Recovering s1_{idx}...")
    s1_int = recover_s1(c_list, d_list)
    s1_recovered.append(s1_int)
    print(f"  s1_{idx} = {s1_int}")

# Verify
print("[*] Verifying recovered s1...")
t0_check = R(0)
t1_check = R(0)
for j in range(l):
    t0_check += A[0][j] * R(s1_recovered[j])
    t1_check += A[1][j] * R(s1_recovered[j])

# Retry loop with more signatures if needed
retry_count = 0
while (t0_check != t[0] or t1_check != t[1]) and retry_count < 5:
    print(f"[-] Verification failed (attempt {retry_count+1}), getting 20 more sigs...")
    retry_count += 1
    for i in range(20):
        msg = f"extra_{retry_count}_{i}"
        c_new, z_new, r_new = get_signature(msg)
        d0_new = [z_new[0][j] - r_new[0][j] for j in range(n)]
        d1_new = [z_new[1][j] - r_new[1][j] for j in range(n)]
        c_list.append(c_new)
        d0_list.append(d0_new)
        d1_list.append(d1_new)

    print(f"[*] Retrying with {len(c_list)} total sigs...")
    for idx, d_list in enumerate([d0_list, d1_list]):
        s1_int = recover_s1(c_list, d_list)
        s1_recovered[idx] = s1_int
        print(f"  s1_{idx} = {s1_int}")

    t0_check = R(0)
    t1_check = R(0)
    for j in range(l):
        t0_check += A[0][j] * R(s1_recovered[j])
        t1_check += A[1][j] * R(s1_recovered[j])

if t0_check == t[0] and t1_check == t[1]:
    print("[+] Secret key recovered successfully!")
else:
    print("[-] Failed to recover s1 after retries, exiting.")
    p.close()
    exit()

# Forge signature
print(f"[*] Forging signature for: {TARGET_MSG}")
c_forged, z_forged = forge_signature(TARGET_MSG, A, t, s1_recovered)
print("[+] Signature forged!")

# Submit
print("[*] Submitting forged signature...")
p.recvuntil(b'> ')
p.sendline(b'3')

p.recvuntil(b'Enter c')
p.recvline()
p.sendline(str(c_forged).encode())

p.recvuntil(b'Enter z[0]')
p.recvline()
p.sendline(str(z_forged[0]).encode())

p.recvuntil(b'Enter z[1]')
p.recvline()
p.sendline(str(z_forged[1]).encode())

# Get flag
print("[*] Waiting for flag...")
try:
    response = p.recvall(timeout=3)
    print(response.decode())
except:
    pass

p.interactive()

'''
#!/usr/bin/env python3
"""
Leaky Dilithium - A vulnerable ML-DSA-like signature service.
"""

import hashlib
import os
import random
import sys

# ================== Parameters ==================
n = 64
q = 65537
k = 2
l = 2
eta = 2
tau = 20
gamma1 = 8192
gamma2 = 256
beta = tau * eta

NOISE_BOUND = 15

TARGET_MSG = "Please give me the flag"
FLAG = os.environ.get("FLAG")


# ================== Polynomial arithmetic ==================
class Poly:
    """Polynomial in Z_q[x]/(x^n+1), stored with coefficients in 0..q-1."""

    def __init__(self, coeffs=None):
        if coeffs is None:
            self.coeffs = [0] * n
        else:
            self.coeffs = [c % q for c in coeffs]
            if len(self.coeffs) != n:
                raise ValueError(f"Length must be {n}")

    def __add__(self, other):
        return Poly([(a + b) % q for a, b in zip(self.coeffs, other.coeffs)])

    def __sub__(self, other):
        return Poly([(a - b) % q for a, b in zip(self.coeffs, other.coeffs)])

    def __mul__(self, other):
        """Convolution modulo x^n+1 and q."""
        res = [0] * (2 * n)
        for i in range(n):
            if self.coeffs[i] == 0:
                continue
            for j in range(n):
                res[i + j] += self.coeffs[i] * other.coeffs[j]

        final = [0] * n
        for i in range(2 * n - 1):
            idx = i % n
            val = res[i] % q
            if i < n:
                final[idx] = (final[idx] + val) % q
            else:
                final[idx] = (final[idx] - val) % q
        return Poly(final)

    def __eq__(self, other):
        return self.coeffs == other.coeffs

    def to_int_list(self):
        return self.coeffs

    def centered_list(self):
        half = q // 2
        return [c if c <= half else c - q for c in self.coeffs]


def poly_vec_add(v1, v2):
    return [a + b for a, b in zip(v1, v2)]


def matrix_vec_mul(mat, vec):
    res = []
    for row in mat:
        acc = Poly()
        for a, v in zip(row, vec):
            acc = acc + (a * v)
        res.append(acc)
    return res


def poly_vec_scalar_mul(c, vec):
    return [c * v for v in vec]


# ================== Helpers ==================
def sample_small_poly():
    return Poly([random.randint(-eta, eta) for _ in range(n)])
# -2 - 2

def sample_uniform_poly():
    return Poly([random.randint(0, q - 1) for _ in range(n)])


def sample_y():
    y = []
    for _ in range(l):
        coeffs = [random.randint(-gamma1 + 1, gamma1) for _ in range(n)] # 64    
        y.append(Poly(coeffs))  # -8191,8192
    return y


def high_bits(r, gamma2):
    r = r % q
    r0 = r % gamma2
    if r0 > gamma2 // 2:
        r0 -= gamma2
    return (r - r0) // gamma2


def poly_high_bits(poly, gamma2):   # 多项式高位提取
    return [high_bits(c, gamma2) for c in poly.coeffs]


def serialize_w1(w1_list):
    data = b""
    for coeffs in w1_list:
        for v in coeffs:
            data += v.to_bytes(2, "big")
    return data


def generate_challenge(msg, w1_list):
    data = msg.encode() + serialize_w1(w1_list)
    seed = hashlib.sha256(data).digest()
    rng = random.Random(seed)

    c_coeffs = [0] * n
    positions = rng.sample(range(n), tau) # 20
    for pos in positions:
        c_coeffs[pos] = 1 if rng.randint(0, 1) == 0 else -1
    return Poly(c_coeffs)


# ================== Key generation ==================
def keygen():
    A = [[sample_uniform_poly() for _ in range(l)] for _ in range(k)] 
    s1 = [sample_small_poly() for _ in range(l)]
    t = matrix_vec_mul(A, s1)
    return A, t, s1


# ================== Signature ==================
def sign(msg, A, s1):
    while True:
        y = sample_y()  # -8191,8192 * 2,类似s1的格式
        w = matrix_vec_mul(A, y)
        w1_list = [poly_high_bits(p, gamma2) for p in w]    # 多项式高位提取
        c = generate_challenge(msg, w1_list)
        cs1 = poly_vec_scalar_mul(c, s1)    # c * s1
        z = poly_vec_add(y, cs1)    # y + cs1

        z_centered = [coeff for p in z for coeff in p.centered_list()]  
        # centered_list() 将多项式系数从 [0, q-1] 的范围转换为 [-(q-1)/2, (q-1)/2] 的范围

        if max(abs(v) for v in z_centered) >= gamma1 - beta: # 8192 - 20*2
            continue

        noise = [   # -15 - 15
            [random.randint(-NOISE_BOUND, NOISE_BOUND) for _ in range(n)]
            for _ in range(l)
        ]
        r = [Poly([y[i].coeffs[j] + noise[i][j] for j in range(n)]) for i in range(l)]
        return c, z, r


# ================== Verification ==================
def verify(msg, c, z, A, t):
    z_centered = [coeff for p in z for coeff in p.centered_list()]
    if max(abs(v) for v in z_centered) >= gamma1 - beta:
        return False

    Az = matrix_vec_mul(A, z)
    ct = poly_vec_scalar_mul(c, t)
    w_prime = [Az[i] - ct[i] for i in range(k)]
    w1_prime = [poly_high_bits(p, gamma2) for p in w_prime]
    c_prime = generate_challenge(msg, w1_prime)
    return c == c_prime


# ================== Server interaction ==================
def main():
    random.seed(os.urandom(8))
    print("=== Leaky Dilithium Signature Service ===", flush=True)
    A, t, s1 = keygen()
    print("[+] Key generated.", flush=True)

    while True:
        print("\nMenu:", flush=True)
        print("1. Get public key", flush=True)
        print("2. Request signature", flush=True)
        print("3. Submit admin signature", flush=True)
        print("0. Exit", flush=True)
        choice = input("> ").strip()

        if choice == "1":
            print("Public key (A, t):", flush=True)
            print("A:", flush=True)
            for row in A:
                for poly in row:
                    print(poly.to_int_list(), flush=True)
            print("t:", flush=True)
            for poly in t:
                print(poly.to_int_list(), flush=True)

        elif choice == "2":
            msg = input("Message to sign: ").strip()
            if msg == TARGET_MSG:
                print("[-] Sorry, cannot sign the target message!", flush=True)
                continue

            c, z, r = sign(msg, A, s1)
            print("Signature:", flush=True)
            print("c:", c.coeffs, flush=True)
            print("z:", flush=True)
            for poly in z:
                print(poly.centered_list(), flush=True)
            print("r (debug):", flush=True)
            for poly in r:
                print(poly.centered_list(), flush=True)

        elif choice == "3":
            print("Submit your signature for: " + TARGET_MSG, flush=True)
            msg = TARGET_MSG
            print("Enter c (list of int, length 64):", flush=True)
            c_data = input().strip()
            try:
                c_coeffs = [int(x) for x in c_data.strip("[]").split(",")]
                c = Poly(c_coeffs)
            except Exception:
                print("Invalid format.", flush=True)
                continue

            z_vec = []
            for i in range(l):  # 2
                print(f"Enter z[{i}] (64 ints):", flush=True)
                z_data = input().strip()
                try:
                    z_coeffs = [int(x) for x in z_data.strip("[]").split(",")]
                    z_vec.append(Poly(z_coeffs))
                except Exception:
                    print("Invalid format.", flush=True)
                    break

            if len(z_vec) != l:
                continue

            if verify(msg, c, z_vec, A, t):
                print("[+] Signature valid! Here is your flag: " + FLAG, flush=True)
            else:
                print("[-] Invalid signature.", flush=True)
            break

        elif choice == "0":
            print("Bye!", flush=True)
            sys.exit(0)
        else:
            print("Unknown option.", flush=True)


if __name__ == "__main__":
    main()


'''