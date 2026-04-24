from gmpy2 import *
from Cryptodome.Util.number import *
from gmpy2 import gmpy2 # gmpy2是一个Python库，旨在提供高精度计算功能，并且支持整数、有理数、浮点数等多种数据类型

enc = 'n]h\]kka[[eiWW_R`bO]]`NMUWWIFXHUCP'

def decrypy4():
    temp = ''
    offset = 5
    for i in range(len(enc)):
        temp += chr(ord(enc[i]) + offset + i)
    return (temp)

def decrypy5(enc):
    for a in range(1,27):
        flag = ''
        for i in enc:
            try:
                s = chr((((ord(i)-97)-7)*gmpy2.invert(a,26))%26+97)
                flag += s
            except:
                break
        print(flag)

decrypy5(decrypy4())








