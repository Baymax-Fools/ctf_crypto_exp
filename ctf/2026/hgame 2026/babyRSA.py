'''
from Crypto.Util.number import *
from gmpy2 import *
from random import *
import string
k = randint(30, 40)
str = string.digits + string.ascii_letters + "_@"
flag = b"VIDAR{" + "".join([choice(str) for i in range(k)]).encode() + b"}"
p = getPrime(120)
q = getPrime(120)
n = p * q
e = 65537
m = bytes_to_long(flag)
c = pow(m, e, n)
print(f'c = {c}')
print(f'p = {p}')
print(f'q = {q}')

'''

from Crypto.Util.number import *
from gmpy2 import *
from random import *
import string

c = 451420045234442273941376910979916645887835448913611695130061067762180161
p = 722243413239346736518453990676052563
q = 777452004761824304315754169245494387
e = 65537

strs = string.digits + string.ascii_letters + "_@"
# 48-57 64-90 95 97-122   

L = (p-1) * (q-1)
d = inverse(e,L)
n = p*q
m0 = int(pow(c,d,n))

c = m0

for k in range(30,40):
    pre = b'VIDAR{'
    suf = b'}'
    
    c = c - 256**(k + 1) * bytes_to_long(pre) - bytes_to_long(suf)
    c = c * inverse(256,n) % n
    
    M = matrix(ZZ,k+2,k+2)
    
    for i in range(k):
        M[i,i] = 1
        M[i,-1] = 256**i
        c -= 85*256**i

    M[-2,-2] = 1
    M[-2,-1] = -c
    M[-1,-1] = n
    M[:,-1:] *= n
    
    res = M.BKZ()
    for r in res:
        if all(abs(j) <= 37 for j in r[:-1]) and abs(r[-2]) == 1:
            flag = ''
            if r[-2] == -1:
                for i in r[:-2]:
                    flag += chr(85 - i)
            flag = flag[::-1]
            print(flag)
    c = m0