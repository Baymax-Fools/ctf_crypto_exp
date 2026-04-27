from Crypto.Util.number import *
from Crypto.Cipher import AES
from tqdm import *
from base64 import *
import hashlib

n, a, b = load(r"F:\download\CTF\eezzdlp\data.sobj")

ct = "Q3UBa1pz1fi35L94peaFbPvpQe4UyXOUif3CKS/CmZdXOiV7bA5NNNjJ1KeUiAFE"
p = 14262553722350428046713771076551090314160260448968748240889092522867981035381835010729957810183043946868290618279293005580111881543857313243691824746036623976338940751627470874113302539

Ap = matrix(Zp(p, 2), a)
Bp = matrix(Zp(p, 2), b)

cpA = Ap.charpoly()
cpB = Bp.charpoly()

def f(x):
    return ZZ(pow(x, p-1, n) - 1) // p

eA = cpA.roots()[0][0].lift()
eB = cpB.roots()[1][0].lift()

k0 = f(eB) * inverse(f(eA), p) % p
print(f'k0 =',k0)


base = pow(eA, p, n)
y = eB * pow(eA, -k0, n) % n

l = (1 << 659) // p
r = (1 << 660) // p

mid = (r - l).isqrt() + 1
print(mid)
print(f'len(mid) =',int(mid).bit_length())


table = {}
tmp = 1
for i in trange(mid):
    table[tmp] = i
    tmp = (tmp * base) % n

step = pow(base, -mid, n)
tmp = y * pow(base, -l, n) % n
dl = -1

for i in trange(mid):
    if tmp in table:
        dl = l + i * mid + table[tmp]
        break
    tmp = (tmp * step) % n

k = k0 + dl * p
key = hashlib.md5(long_to_bytes(k)).digest()
cipher = AES.new(key, AES.MODE_ECB)
flag = cipher.decrypt(b64decode(ct))
print(flag)


'''
from Crypto.Util.number import long_to_bytes, getPrime
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
from base64 import b64encode
import hashlib
from sage.all import *
from secret import getRandomMatrix, get_random_prime

with open('flag.txt', 'rb') as f:
    flag = pad(f.read(), AES.block_size)

p = get_random_prime()
q = get_random_prime()
n = p * p

a = Matrix(Zmod(n), getRandomMatrix())

k = getPrime(660)
b = a ** k

data = [n, a, b]
save(data, "data.sobj")

key = hashlib.md5(long_to_bytes(k)).digest()

cipher = AES.new(key, AES.MODE_ECB)
ciphertext = cipher.encrypt(flag)

print(b64encode(ciphertext).decode())
# Q3UBa1pz1fi35L94peaFbPvpQe4UyXOUif3CKS/CmZdXOiV7bA5NNNjJ1KeUiAFE
'''