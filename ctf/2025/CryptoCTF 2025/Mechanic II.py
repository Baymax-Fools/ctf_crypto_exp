from pwn import *
from sage.all import *
from Crypto.Util.number import *
from hashlib import sha1
from ast import literal_eval
import string
from tqdm import trange

p = remote("node1.anna.nssctf.cn",26997)
#context(log_level='debug')

def diffpow(head,h):
    charset = string.printable[:63] + '_'

    for i in charset:
        for j in charset:
            for x in charset:
                for y in charset:
                    tail = i+j+x+y
                    temp = hashlib.sha3_256((head+tail).encode()).hexdigest()
                    if temp == h:
                        print("tail =",tail)
                        return tail       



p.recvuntil(b'first: (')
rec = p.recvline().strip()[:-1].decode()
rec = rec.split(',')

head = rec[0][2:-1]
h = rec[1][2:-1]

print(head)
print(h)

tail = diffpow(head,h).encode()
p.sendline(tail)

for i in trange(1337):
    p.recvuntil(b"[Q]uit\n")
    p.sendline(b"d")
    p.sendline(str(i).encode())
    p.recvuntil(b"_shasec = ")
    ss1 = p.recvline().strip().decode()

    p.recvuntil(b"[Q]uit\n")
    p.sendline(b"r")
    p.sendline(str(i).encode())

    p.recvuntil(b"[Q]uit\n")
    p.sendline(b"d")
    p.sendline(str(i+1337).encode())
    p.recvuntil(b"_shasec = ")
    ss2 = p.recvline().strip().decode()
    
    if(ss1 == ss2):
        shasec = literal_eval(ss1)
        secret = hashlib.sha3_256(shasec + hashlib.sha3_256(shasec + str(i).encode()).digest()).hexdigest()
        p.recvuntil(b"[Q]uit\n")
        p.sendline(b"s")
        p.sendline(secret.encode())
        p.recvuntil(b"Congrats, you got the flag: ")
        print(p.recvline())
        break

p.interactive()


'''
#!/usr/bin/env python3

from quantcrypt.kem import MLKEM_1024
import sys, os, string
from random import randint
import hashlib
from flag import flag

def die(*args):
	pr(*args)
	quit()
	
def pr(*args):
	s = " ".join(map(str, args))
	sys.stdout.write(s + "\n")
	sys.stdout.flush()
	
def sc():
	return sys.stdin.buffer.readline()

def rand_str(l):
	charset = string.printable[:63] + '_'
	return ''.join([charset[randint(0, 63)] for _ in range(l)]).encode()

def pow():
	head = rand_str(15)
	tail = rand_str(4)
	h = hashlib.sha3_256(head + tail).hexdigest()
	return head, h

def main():
	border = "┃"
	pr(        "┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓")
	pr(border, ".:::       Welcome to the Mechanic II cryptography task!      ::.", border)
	pr(border, "Your mission is to find flag by analyzing this amazing Oracle! :)", border)
	pr(        "┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛")
	head, h = pow()
	pr(border, f'Please pass the proof of work first: {head, h}')
	_tail = sc().strip()
	if hashlib.sha3_256(head + _tail).hexdigest() == h:
		_b = True
	else:
		die(border, 'Your should pass the POW! Bye!!')
	kem = MLKEM_1024()
	c, n = 0, 1337
	KEY_PAIR = [kem.keygen() for _ in range(n)]
	SKEYS = [KEY_PAIR[_][1] for _ in range(n)]	# 1337个私钥
	r = randint(0, n - 1)
	cipher, shasec = kem.encaps(KEY_PAIR[r][0])
	secret = hashlib.sha3_256(shasec + hashlib.sha3_256(shasec + str(r).encode()).digest()).hexdigest()
	while _b:
		if c > 3 * 1337:
			die(border, 'The server is need to rest :/')
		pr(f"{border} Options: \n{border}\t[D]ecrypt cipher \n{border}\t[R]andomize a secret key! \n{border}\t[S]ubmit the secret \n{border}\t[Q]uit")
		ans = sc().decode().strip().lower()
		c += 1
		if ans == 'd':
			pr(border, 'Please select an ID: ')
			_id = sc().decode().strip()
			try:
				_id = int(_id)
				_shasec = kem.decaps(SKEYS[_id], cipher)
			except:
				die(border, 'Your input ID is invalid! Bye!!')
			pr(border, f'{_shasec = }')
		elif ans == 'r':
			pr(border, 'Please select an ID: ')
			_id = sc().decode().strip()
			try:
				_id = int(_id)
				_skey = SKEYS[_id][:-32] + os.urandom(32)
			except:
				die(border, 'Your input ID is invalid! Bye!!')
			SKEYS.append(_skey)
		elif ans == 's':
			pr(border, 'Please send the secret: ')
			_secret = sc().decode().strip()
			if _secret == secret:
				die(border, f'Congrats, you got the flag: {flag}')
			else:
				die(border, 'Your secret is incorrect! Bye!!')
		elif ans == 'q':
			die(border, "Quitting...")
		else:
			die(border, "Bye...")

if __name__ == '__main__':
	main()
'''