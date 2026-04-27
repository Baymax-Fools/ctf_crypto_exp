from Crypto.Util.number import *
from tqdm import *
from random import *

f = open(r"F:\download\CTF\task\task\output.txt",'r')
data = eval(f.read())
f.close()

n, m = 25, 15
q = 256708627612544299823733222331047933697

def solve(s):
    b = []
    A = []

    for l in s:
        A.append(l[:-1])
        b.append(l[-1])

    A = matrix(GF(q), A)

    kerA = A.left_kernel().basis()
    L = block_matrix(ZZ, [[matrix(kerA)], [q]])
    res = L.BKZ()[20]

    u = vector(GF(q), res)
    ub = u * vector(GF(q), b)

    if(ub > q//2):
        ub = q - ub

    if abs(int(ub)).bit_length() < 100:
        return True
    else:
        return False

idx = [i for i, _ in enumerate(data)]

while True:
    s = []
    idxs = choices(idx, k=3)
    if len(set(idxs)) < 3:
        continue
    for i in idxs:
        s += data[i]
    if solve(s):
        print(idxs)
        break

m = ""
for i in tqdm(idx):
    if i in idxs:
        m += "1"
        continue
    else:
        tmp = data[idxs[0]] + data[idxs[1]] + data[i]
        if solve(tmp):
            m += "1"
        else:
            m += "0"

flag = int(m, 2).to_bytes(25, "little").decode()
print("hgame{" + flag + "}")

'''
from Crypto.Util.number import *
from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler
from sage.crypto.lwe import LWE
from secret import flag

flagbin = bin(int.from_bytes(flag.split(b'hgame{')[1][:-1], 'little'))[2:].rjust(25 * 8, "0")

n, m = 25, 15
q=getPrime(128)
F = GF(q)
V = VectorSpace(F, n)
D = DiscreteGaussianDistributionIntegerSampler(2**16) 
lwe = LWE(n=n, q=q, D=D)

def encrypt_bit(bit): # 0 or 1
    if bit == 1:
        samples_list = [lwe() for _ in range(m)]
        return [tuple(list(a) + [b]) for a, b in samples_list]
    else:
        return [tuple([F.random_element() for _ in range(n + 1)]) for _ in range(m)]

encbit = []
for bit in flagbin:
    encbit.append(encrypt_bit(int(bit)))

with open("./output", "wb") as f:
    f.write(str(encbit).encode())

# q = 256708627612544299823733222331047933697
'''