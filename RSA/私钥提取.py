from Crypto.PublicKey import RSA

# 读取私钥
with open(r'F:\download\CTF\key.pem', 'r') as f:
    key = RSA.import_key(f.read())

print("Modulus:", key.n)
print("Public Exponent:", key.e)
print("Private Exponent:", key.d)
print("Prime p:", key.p)
print("Prime q:", key.q)

# from Crypto.PublicKey import RSA

# # 1. 读取并导入私钥（你已有的代码）
# with open(r'C:\Users\Baymax\Desktop\public.pem', 'r') as f:
#     pkey = RSA.import_key(f.read())

# n = pkey.n
# e = pkey.e

# print("Modulus (n):", n)
# print("Public Exponent (e):", e)