dict_map = {0: 'J', 1: 'K', 2: 'L', 3: 'M', 4: 'N', 5: 'O', 6: 'x', 7: 'y', 8: 'U', 9: 'V', 10: 'z', 11: 'A', 12: 'B', 13: 'C', 14: 'D', 15: 'E', 16: 'F', 17: 'G', 18: 'H', 19: '7', 20: '8', 21: '9', 22: 'P', 23: 'Q', 24: 'I', 25: 'a', 26: 'b', 27: 'c', 28: 'd', 29: 'e', 30: 'f', 31: 'g', 32: 'h', 33: 'i', 34: 'j', 35: 'k', 36: 'l', 37: 'm', 38: 'W', 39: 'X', 40: 'Y', 41: 'Z', 42: '0', 43: '1', 44: '2', 45: '3', 46: '4', 47: '5', 48: '6', 49: 'R', 50: 'S', 51: 'T', 52: 'n', 53: 'o', 54: 'p', 55: 'q', 56: 'r', 57: 's', 58: 't', 59: 'u', 60: 'v', 61: 'w', 62: '+', 63: '/', 64: '='}

rev_dict = {v: k for k, v in dict_map.items()}

cipher = "FlZNfnF6Qol6e9w17WwQQoGYBQCgIkGTa9w3IQKw"

# 转成数字列表
indexes = [rev_dict[ch] for ch in cipher]

# 解码为字节
def decode_custom_base64(indexes):
    bytes_out = []
    for i in range(0, len(indexes), 4):
        chunk = indexes[i:i+4]
        if len(chunk) < 4:
            break
        n = (chunk[0] << 18) | (chunk[1] << 12) | (chunk[2] << 6) | chunk[3]
        bytes_out.append((n >> 16) & 0xFF)
        bytes_out.append((n >> 8) & 0xFF)
        bytes_out.append(n & 0xFF)
    # 去除填充导致的多余零字节（根据实际情况调整）
    # 这里先全部输出，再看情况
    return bytes(bytes_out)

decoded_bytes = decode_custom_base64(indexes)
print(decoded_bytes)

# 尝试以字符串显示
try:
    print(decoded_bytes.decode('utf-8'))
except:
    print(decoded_bytes)  # 如果非 UTF-8，可能是二进制数据