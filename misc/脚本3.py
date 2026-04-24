import base64
from pwn import xor

c1 = base64.b64decode("RHAnQ+wq/IYrbQxBjitOAA==")
c2 = base64.b64decode("naEDQikgph4uQEpZSnvCHg==")

# 得到 key2
k2 = xor(c2, b"A"*16)

def movekey(k, shift):
    return k[shift:] + k[:shift]

for offset in range(1, 16):
    k1 = movekey(k2, offset)
    m = xor(c1, k1)
    print(m)