# 解密映射
decrypt_map = {
    'A': 'E', 'B': 'G', 'C': 'F', 'D': 'A', 'E': 'B', 'F': 'C', 'G': 'D',
    'H': 'L', 'I': 'N', 'J': 'I', 'K': 'H', 'L': 'K', 'M': 'J', 'N': 'M',
    'O': 'O', 'P': 'P', 'Q': 'Q', 'R': 'R', 'S': 'S', 'T': 'T', 'U': 'U',
    'V': 'V', 'W': 'W', 'X': 'X', 'Y': 'Y', 'Z': 'Z'
}

ciphertext = "SUFK_D_SJNPHA_PARNUTDTJOI_WJHH_GACJIJTAHY_IOT_STUNP_YOU."

plaintext = ""
for ch in ciphertext:
    if ch.isalpha():
        plaintext += decrypt_map[ch]
    else:
        plaintext += ch

print("密文:", ciphertext)
print("明文:", plaintext)