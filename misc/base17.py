def decode(base17):
    base17 = base17.lower()
    qb = "0123456789abcdefg"
    map = {c:i for i,c in enumerate(qb)}
    num = 0
    for c in base17:
        num = num * 17 + map[c]
    return num.to_bytes((num.bit_length() + 7) // 8,'big')

print(decode("807G6F429C7FA2200F46525G1350AB20G339D2GB7D8"))





