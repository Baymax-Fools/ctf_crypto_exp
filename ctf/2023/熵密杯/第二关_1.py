from base64 import b64encode
from Crypto.Util.number import *

p = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF
a = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFC
Gx = 0x32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7
Gy = 0xBC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0
n = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123

d = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF % n

def modinv(k, mod):
    return pow(k, -1, mod)

def point_add(P, Q):
    if P is None: return Q
    if Q is None: return P
    px, py = P; qx, qy = Q
    if px == qx and py == qy:
        lam = (3 * px * px + a) * modinv(2 * py, p) % p
    else:
        lam = (qy - py) * modinv(qx - px, p) % p
    rx = (lam * lam - px - qx) % p
    ry = (lam * (px - rx) - py) % p
    return rx, ry

def point_mul(k, P):
    R = None; T = P
    while k:
        if k & 1: R = point_add(R, T)
        T = point_add(T, T); k >>= 1
    return R

Qx, Qy = point_mul(d, (Gx, Gy))
pub = "04{:064x}{:064x}".format(Qx, Qy)

print("私钥 d =", hex(d))
print("公钥   =", pub)
print("X      = {:064x}".format(Qx))
print("Y      = {:064x}".format(Qy))

print("Encoded private key:", b64encode(long_to_bytes(2**256-1)))