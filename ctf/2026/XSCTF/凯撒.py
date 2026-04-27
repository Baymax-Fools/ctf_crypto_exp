from Cryptodome.Util.number import isPrime

c = "MJSIQC{Kt5s_DPIOtO_k1iRyq_cRm_1eI_Tet6sT_cnybmE}"

def dec(c, r):
    m = ''
    offset = 33550336
    for i, ch in enumerate(c):
        offset += i**2 + r

        if 'a' <= ch <= 'z':
            m += chr((ord(ch) - ord('a') - offset) % 26 + ord('a'))
        elif 'A' <= ch <= 'Z':
            m += chr((ord(ch) - ord('A') - offset) % 26 + ord('A'))
        else:
            m += ch
    return m

for r in range(2048, 4096):
    if not isPrime(r):
        continue
    m = dec(c, r)

    print(m)