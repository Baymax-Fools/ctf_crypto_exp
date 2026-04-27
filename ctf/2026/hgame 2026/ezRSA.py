#!/usr/bin/env python3
from pwn import *
from Crypto.Util.number import *
from base64 import *
def encrypt(plain, x):
    # menu
    data = r.recv(400)
    # print(data.decode())

    r.sendline(b'1')
    data = r.recvline()
    
    r.sendline(str(plain).encode())
    data = r.recvline()
    # print(data.decode())

    # 发送明⽂和翻转的bit
    r.sendline(str(x).encode())
    data = r.recvline().decode().strip()
    # print(data)
    c1 = bytes_to_long(b64decode(data))
    # print(c1)
    return c1

def decrypt(cipher):
    # menu
    data = r.recv(400)
    # print(data.decode())
    # 
 
    r.sendline(b'2')
    data = r.recvline()
    # print(data.decode())

    r.sendline(str(cipher).encode())
    data = r.recvline().decode().strip()
    # print(data)
    p1 = bytes_to_long(b64decode(data))
    # print(p1)
    return p1

def getFlag():
    # menu
    data = r.recv(400)
    # print(data.decode())
    r.sendline(b'3')
    data = r.recvline().decode().strip()
    # print(data)
    f = bytes_to_long(b64decode(data))
    # print(f)
    return f
r = remote('forward.vidar.club', 30231)
c1 = encrypt(2, 0)
c1_ = encrypt(4, 0)
c2 = encrypt(3, 0)
c2_ = encrypt(9, 0)
n = GCD(c1**2-c1_, c2**2-c2_)
# 去掉⼀些可能存在的⼩素数因⼦
 
for i in range(2, 1000):
    if n%i==0:
        while n%i==0:
            n=n//i

c = c1 * 2 % n
e_ = [0] * 50  # 暂时先低位在前
 
e_[0] = 1
for i in range(1, 50):
    c_ = encrypt(2, i)
    if c_ * pow(2, 1<<i, n) % n == c:
        e_[i] = 1
    else:
        e_[i] = 0
e_ = e_[::-1]
e = int(''.join(map(str, e_)), 2)
print(e)
print(n)

c = getFlag()
#print(c)
k=0
for i in range(127):
    c=c*pow(256,e,n)%n
    p=decrypt(c)
    k=k*256+(-inverse(n,256)*p%256)

print(long_to_bytes(k*n//256**127).decode(errors='ignore'))


'''
def b64_to_long(s):  
    return bytes_to_long(b64decode(s)) 

flag = b''  

for i in range(127):  
    c0 = c * pow(256, -i*e, n) % n  

    r.sendlineafter(b'Your choice > ', b"2")  
    r.sendlineafter(b'plz give me your ciphertext:\n', str(c0).encode())  

    m0 = (b64_to_long(r.recvline().strip()) - bytes_to_long(flag) * pow(256, -i, n) % n) % 256  

    flag = long_to_bytes(m0) + flag  

log.success(flag.decode())
'''