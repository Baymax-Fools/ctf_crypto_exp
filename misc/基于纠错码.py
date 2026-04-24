from Crypto.Cipher import AES
import hashlib

with open(r'F:\download\CTF\235016_ezECC\ezECC\output.txt', 'r') as f:
    lines = f.readlines()

cipher_str = lines[0].split(': ')[1]
S_str = lines[1].split(': ')[1]
P_str = lines[2].split(': ')[1]
enc_flag_str = lines[3].split(': ')[1]

F = GF(2^8, repr='int')
n, k = 255, 223
cipher = vector(F, [F.fetch_int(x) for x in eval(cipher_str)])
S = matrix(F, 32, 32, [F.fetch_int(x) for x in eval(S_str)])
P = matrix(F, 255, 255, [F.fetch_int(x) for x in eval(P_str)])

# 重建GRS码
C = codes.GeneralizedReedSolomonCode(F.list()[1:], k)
H = C.parity_check_matrix()

# 核心解密步骤
# 消除S的影响 (S⁻¹ × cipher)
y = S.inverse() * cipher

from sage.coding.grs_code import GRSBerlekampWelchDecoder
decoder = GRSBerlekampWelchDecoder(C)

# 构造一个向量，其校验子为y，然后解码
v = H.solve_right(y)  # H × v = y
codeword = decoder.decode_to_code(v)  # 找到最近的码字
e_prime = v - codeword  # 得到 P × e

# 消除P的影响 (P⁻¹ × e_prime)
e = P.inverse() * e_prime         # 这个e是key打乱后的

key_list = [x.integer_representation() for x in e]
key_digest = hashlib.sha256(str(key_list).encode()).digest()

aes = AES.new(key_digest, AES.MODE_ECB)
flag = aes.decrypt(eval(enc_flag_str))

print(f"Flag: {flag.decode()}")