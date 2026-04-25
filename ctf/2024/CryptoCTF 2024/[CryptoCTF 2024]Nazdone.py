'''
#!/usr/bin/env python3

from Crypto.Util.number import *
from random import *
from secret import params, flag

def sol(m, a, z):
	p = m * (a - 1) % 2 + 1
	while True:
		R = list(range(1, a))
		shuffle(R)
		for r in R[:z]:
			p += getRandomRange(0, 2) * m ** r
		if isPrime(p):
			return p
		else:
			p = m * (a - 1) % 2 + 1


p, q, r = [sol(*params) for _ in '007']
n = p * q * r
m = bytes_to_long(flag)
c = pow(m, params[0] ** 3 + params[2] - 2, n)
print(f'n = {n}')
print(f'c = {c}')
'''

from Crypto.Util.number import *

n = 301929748923678449872944933611657670834216889867340028357609265175830693931365828840717548752313862343315133541384709574659039910206634528428504034051556622114290811586746168354731258756502196637977942743110508997919976400864419640496894428180120687863921269087080600917900477624095004141559042793509244689248253036809126205146653922738685595903222471152317095497914809983689734189245440774658145462867680027337
c = 104375152140523502741159687674899095271676058870899569351687154311685938980840028326701029233383897490722759532494438442871187152038720886122756131781086198384270569105043114469786514257765392820254951665751573388426239366215033932234329514161827069071792449190823827669673064646681779764841034307000600929149689291216313319444583032339045277433847691961234044840927155960887984372868669401051358701522484473320

table = []

for i in range(2,1000):
    if (n-1) % i == 0 or (n-8)% i == 0:
        table.append(i)

def get_base(n,m):
    sets = []
    while n:
        ai = n % m
        n = n // m
        sets.append(ai)
    return sets

PR.<x> = PolynomialRing(ZZ)

for m in table:
    f = PR(get_base(n,m))
    p = f.factor()
    pqr = []
    
    for poly,_ in p:
        poly = poly(m)
        pqr += [poly]
        
    if len(pqr) == 3:
        p,q,r = pqr
        print(p*q*r == n)
        
        L = (p-1)*(q-1)*(r-1)
        for a in range(1000):
            e = m**3 + a -2
            try:
                print(a)
                #e = m**3 + a -2
                d = inverse(e,L)
                flag = pow(c,d,n)
                print(long_to_bytes(int(flag)))
            except:
                continue
