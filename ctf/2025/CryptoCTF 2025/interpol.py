with open(r'F:\download\CTF\interpol_294c02588bda413403f6ded64c62bcd73f75435e\interpol\output.raw','rb') as read:
    poly = read.read()

poly = loads(poly)

n = 0
while 1:
    x = -(n+1)
    y = poly(x)
    
    if y.is_integer():
        n+=1
    else:
        break

def get_point(i):
    # [(-(1 + (19*n - 14) % len(flag)), ord(flag[(63 * n - 40) % len(flag)]))]
    x= -(1 + (19*i - 14) % n)
    ord_tmp = (63*i-40) % n 
    return x,ord_tmp

m = [0 for _ in range(n)]
for i in range(n):
    x,ord_tmp = get_point(i)
    y = poly(x)
    m[ord_tmp] = y

m = "".join(chr(i) for i in m ) 
print(m)

'''
#!/usr/bin/env sage

from Crypto.Util.number import *
from flag import flag

def randpos(n):
	if randint(0, 1):
		return True, [(-(1 + (19*n - 14) % len(flag)), ord(flag[(63 * n - 40) % len(flag)]))]
	else:
		return False, [(randint(0, 313), (-1) ** randint(0, 1) * Rational(str(getPrime(32)) + '/' + str(getPrime(32))))]

c, n, DATA = 0, 0, []
while True:
	_b, _d = randpos(n)
	H = [d[0] for d in DATA]
	if _b:
		n += 1
		DATA += _d
	else:
		if _d[0][0] in H: continue
		else:
			DATA += _d
			c += 1
	if n >= len(flag): break

A = [DATA[_][0] for _ in range(len(DATA))]
poly = QQ['x'].lagrange_polynomial(DATA).dumps()
f = open('output.raw', 'wb')
f.write(poly)
f.close()
'''