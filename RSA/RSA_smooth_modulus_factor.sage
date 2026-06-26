from sage.all import *
from Crypto.Util.number import *
from itertools import count
from sympy import primerange

# williams's p+1 factorization
def mlucas(v, a, n):
    v1, v2 = v, (v ** 2 - 2) % n
    for bit in bin(a)[3:]:
        if bit == "0":
            v1, v2 = (v1 ** 2 - 2) % n, (v1 * v2 - v) % n
        else:
            v1, v2 = (v1 * v2 - v) % n, (v2 ** 2 - 2) % n
    return v1

# 素数生成器
def primegen():
    yield from primerange(2, 10**6)  # 生成到 10^6 的素数，够用了

# 整数对数：ilog(x, b) = 最大整数 l，使得 b^l <= x
def ilog(x, b):
    l = 0
    while x >= b:
        x //= b
        l += 1
    return l

# Williams p+1 分解攻击
def Williams_p_plus_1_attack(n):
    for v in count(1):  # 不断尝试新的 v
        for p in primegen():
            e = ilog(isqrt(n), p)
            if e == 0:
                break
            for _ in range(e):
                v = mlucas(v, p, n)
            g = gcd(v - 2, n)
            if 1 < g < n:
                return int(g), int(n // g)
            if g == n:
                break

# 开始攻击
p1, q1 = Williams_p_plus_1_attack(n)
if p1 and q1:
    print("williams's p+1 factorization successful!")
    print(f"p = {p1}")
    print(f"q = {q1}")

# pollard's p-1 factorization
def pollard_p_minus_1(n, B=10**5): # B为素数表的上限,可以根据实际往上调
    a = 2  # 通常选2作为基
    for p in primerange(2, B):
        e = int(isqrt(n).bit_length() / p.bit_length())
        a = pow(a, pow(p, e), n)
    g = gcd(a - 1, n)
    if 1 < g < n:
        return g, n // g
    else:
        return None

p2, q2 = pollard_p_minus_1(n)
if p2 and q2:
    print("pollard's p-1 factorization successful!")
    print(f"p = {p2}")
    print(f"q = {q2}")
phi = (p1 - 1) * (q1 - 1)
d = inverse(e, phi)
m = pow(c, d, n)
print(long_to_bytes(m))
# flag{smoothness_is_important}
