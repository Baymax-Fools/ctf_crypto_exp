
from Cryptodome.Cipher import AES

from Crypto.Util.Padding import pad

c=b'\xf8\x15\xc4\xbe\xbe\x1c\x15{\xc8\x1d\x90\xba\xf8B\x19]\x00l\xa7jY\xa2\x05\xad\xed\x07\x05E\xf7\xce\xf8\x96\xbd\x9a\x82\xa4&\xceq\xeb3\xe9\xa1\x0e!\x18(\xa6'
iv=b'\xd1\xdf\x8f)\x08w\xde\xf9yX%\xca[\xcb\x18\x80'
for i in range(2**25):
    key = str(i).encode('utf-8')
    key = pad(key, AES.block_size)
    aes_ecb = AES.new(key, AES.MODE_ECB)

    m=aes_ecb.decrypt(c)

    if b"XSWCTF" in m :
        print(m)







