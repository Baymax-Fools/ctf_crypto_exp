# 出题人对 openssl 项目中的 crypto/rand/drbg_lib.c 文件中一个生成随机数的函数进行了修改，将原本生成32字节随机数写死了，

from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey
from cryptography.hazmat.primitives import serialization

rand0 = [0x67,0xc6,0x69,0x73,0x51,0xff,0x4a,0xec,0x29,0xcd,0xba,0xab,0xf2,0xfb,0xe3,0x46,
         0x7c,0xc2,0x54,0xf8,0x1b,0xe8,0xe7,0x8d,0x76,0x5a,0x2e,0x63,0x33,0x9f,0xc9,0x9a]

sk = "".join(hex(i)[2:].rjust(2, '0') for i in rand0)
print(sk)   # 服务端的私钥

privatekey = X25519PrivateKey.from_private_bytes(bytes.fromhex(sk))
# X25519PrivateKey.from_private_bytes(...) 将这个字节序列构造为一个 X25519PrivateKey 对象。
# 这个对象封装了私钥，并可直接用于后续操作（如生成公钥、执行 ECDH 交换等）。

print(privatekey.public_key().public_bytes(
    encoding=serialization.Encoding.Raw,
    format=serialization.PublicFormat.Raw
).hex())    # 服务端的公钥
# privatekey.public_key() 从私钥对象派生出对应的 X25519 公钥对象。
# 然后调用 .public_bytes(...) 将公钥以原始字节形式导出：
# encoding=serialization.Encoding.Raw 表示不添加任何包装头或长度信息，直接输出原始密钥字节。
# format=serialization.PublicFormat.Raw 表示公钥的格式也是原始的（对 X25519 来说就是 32 字节的 X 坐标）

########################################################3

client_publickey = X25519PublicKey.from_public_bytes(bytes.fromhex('a0022027e0390ead7d82e1e74ae2d2f045fbf72896b9846d7f28bfa184280e3e'))

result = privatekey.exchange(client_publickey)
#print(result.hex())

# random: 9d8f92cc2ac8f33293da5169d49c82794c660fc937bd0c1b05f5e062e491da85   32字节

# 预主密钥的格式为 PMS_CLIENT_RANDOM[空格]Random[空格]sharekey
key1 = "PMS_CLIENT_RANDOM 9d8f92cc2ac8f33293da5169d49c82794c660fc937bd0c1b05f5e062e491da85 7ff739dbe782d963e54e3242d83b3a01a6535aed3579f6a514a664b363915903"
print(key1)

client_publickey_2 = X25519PublicKey.from_public_bytes(bytes.fromhex('6bfa302f9973d1e6eca242dd65e45738f8539efe75eb424e91a8482759dcf732'))
reslut_2 = privatekey.exchange(client_publickey_2)
# print(reslut_2.hex())

key2 = "PMS_CLIENT_RANDOM b5dbfb40bc4c2b1a46bbc594fc89a56c17fe7db891beb7c111691516bd3117d1 4c8c1680018a8dd48749d642b6a6df5cc2104cb98842b82b0d748430108b8f61"
print(key2)

"""
POST /api/login HTTP/1.1
Host: 172.80.0.11
User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:109.0) Gecko/20100101 Firefox/115.0
Accept: application/json, text/plain, */*
Accept-Language: zh-CN,zh;q=0.8,zh-TW;q=0.7,zh-HK;q=0.5,en-US;q=0.3,en;q=0.2
Accept-Encoding: gzip, deflate, br
Content-Type: application/json
Content-Length: 51
Origin: https://172.80.0.11
Connection: keep-alive
Referer: https://172.80.0.11/
Sec-Fetch-Dest: empty
Sec-Fetch-Mode: cors
Sec-Fetch-Site: same-origin

{"username":"admin1","password":"KPFZucey@^(&8526"}
HTTP/1.1 200 OK
Server: nginx/1.24.0
Date: Tue, 18 Jul 2023 07:29:11 GMT
Content-Type: application/json; charset=utf-8
Content-Length: 266
Connection: keep-alive

{"code":1,"flag":"flag3{d30e5a41-ce9a-7948-a9ab-bd7924d45bf1}","msg":"...............","token":"eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJuYW1lIjoiYWRtaW4xIiwiZXhwIjoxNjg5NzUxNzUxLCJpc3MiOiJxZnpoZSIsIm5iZiI6MTY4OTY2NTM1MH0.nYO0m4gf2sd3XVAm7arsMdZb3TRhFC2cS9-Xb2pbFO8"}
"""