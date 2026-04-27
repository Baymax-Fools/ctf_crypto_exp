import string

# 已知的密文-明文对（从解密结果中提取）
ciphertext = """esnrr'w drlhw cwhl htvq. kvt aaohxw zq wfdkl kf amd zvft kgs pbpvg nwie xkow. lv krr cbnar livq jc bxfu tamejj vt iagew xf hrh dk gje mesov: fdxkp bxiw, ufohq udivovq, gcgh udoiw rqu zpjt yhhtj, vrihxyas, uetre oca kpeto, srzzta hkttxfhj, 47xmb187vhoco8ko5lfjrot7y4w4292ki06yjwk6fl5b4aazoos9g4l9sqg1rdueydodlcomhhh74qkfuezkvrewtc8gaey4syrakkae27qe97ya49pwrtfhz, glsot iskdkctp, xnixw, priyheane iyugzbv, mwws, veiufhh, djwvr, ovwtvjm, sjd, ysi vfat plnagkv uvohlf, leitvudwcq zqmuyxv."""

# 已知的正确明文开头（根据上下文推测）
known_plain_start = "harry's mouth fell open. the dishes in front of him were now piled with food. he had never seen so many things he liked to eat on one table: roast beef, roast chicken, pork chops and lamb chops, sausages, bacon and steak, boiled potatoes, "


def recover_key(ciphertext, known_plain, key_length=11):
    """从已知明文恢复密钥"""
    key = ['?'] * key_length
    k_index = 0

    for i, (c, p) in enumerate(zip(ciphertext, known_plain)):
        if c in string.ascii_lowercase:
            if p in string.ascii_lowercase:
                # 计算密钥字母
                key_shift = (ord(c) - ord(p)) % 26
                key_char = chr(key_shift + ord('a'))

                # 更新密钥
                if key[k_index % key_length] == '?':
                    key[k_index % key_length] = key_char
                elif key[k_index % key_length] != key_char:
                    print(f"密钥冲突: 位置 {k_index % key_length}, 原有: {key[k_index % key_length]}, 新: {key_char}")

            k_index += 1

    return ''.join(key)


# 恢复密钥
recovered_key = recover_key(ciphertext, known_plain_start)
print(f"恢复的密钥: {recovered_key}")


# 用恢复的密钥解密
def vigenere_decrypt(ct, key):
    pt = ""
    k = 0
    for c in ct:
        if c in string.ascii_lowercase:
            shift = ord(key[k % len(key)]) - ord('a')
            pt += chr((ord(c) - ord('a') - shift) % 26 + ord('a'))
            k += 1
        else:
            pt += c
    return pt


plaintext = vigenere_decrypt(ciphertext, recovered_key)
print("\n解密结果:")
print(plaintext)

# 提取 base36 部分
import re

m = re.search(r"[0-9a-z]{40,}", plaintext)
if m:
    base36_str = m.group(0)
    print(f"\nBase36 字符串: {base36_str}")

    # 转换为 bytes
    flag_int = int(base36_str, 36)
    flag_bytes = flag_int.to_bytes((flag_int.bit_length() + 7) // 8, 'big')
    print(f"Flag: {flag_bytes}")