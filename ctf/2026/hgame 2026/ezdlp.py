data = load(r"F:\download\CTF\ezdlp\data.sobj")

n = data[0]
a = data[1]
b = data[2]

p = 282964522500710252996522860321128988886949295243765606602614844463493284542147924563568163094392590450939540920228998768405900675902689378522299357223754617695943
q = 511405127645157121220046316928395473344738559750412727565053675377154964183416414295066240070803421575018695355362581643466329860038567115911393279779768674224503

def bsgs(G,kG,p,order):
    t = int(sqrt(order)) + 2
    dic = {}
    
    tG = pow(G,t,p)
    atG = 1
    for a in range(t):
        dic[atG] = a
        atG = (atG * tG) % p
        
    bG = kG
    _G = pow(G,(-1) % order,p)
    
    for b in range(t):
        if bG in dic:
            return t * dic[bG] + b
        bG = (bG * _G) % p
    
    
def pohlig_hellman(G,kG,p,order):
    facs = list(factor(order))
    qs = []
    ord_q = []
    for q,exp in facs:
        qs.append(q^exp)
        ord_q.append(bsgs(pow(G,order//(q^exp),p),pow(kG,order//(q^exp),p),p,q^exp))
    return crt(ord_q,qs)
    
def dlp(G,kG):
    ord_l = [p-1,q-1]
    p_l = [p,q]
    qs = []
    ord_q = []
    for i in range(len(p_l)):
        qs.append(ord_l[i])
        ord_q.append(pohlig_hellman(G,kG,p_l[i],ord_l[i]))
    return crt(ord_q,qs)

k = dlp(a.det(),b.det())
print(k)

'''
from Crypto.Util.number import long_to_bytes, getPrime
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
from base64 import b64encode
import hashlib
from sage.all import *
from secret import getRandomMatrix

with open('flag.txt', 'rb') as f:
    flag = pad(f.read(), AES.block_size)

# Want to factor n? I've already done it! Get it yourself.
n = 144709507748526661267852152217031923282704243254105275252262414154410511284347828603240755427862752297392095652561239549522158121842455510674435510821274029842500154931546666242034086499872050823824437303603895977092291834159890433746969317535636398062008995784281741721729948231010601796589449187553147904043991226174291329
a = Matrix(Zmod(n), getRandomMatrix())

k = getPrime(1000)
b = a ** k

data = [n, a, b]
save(data, "data.sobj")

key = hashlib.md5(long_to_bytes(k)).digest()

cipher = AES.new(key, AES.MODE_ECB)
ciphertext = cipher.encrypt(flag)

print(b64encode(ciphertext).decode())
# ieJNk5335o9lCy6Ar2XymrDy+HVHcQhikluNSra0kBafw1WDCyyuNPkLACeBsavy

'''