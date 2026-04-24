#!python3
# -*- coding: utf-8 -*-
# @Time : 2020/10/25 21:59
# @Author : A.James
# @FileName: exp2.py
from random import Random

# right shift inverse
def inverse_right(res,shift,bits=32):
    tmp = res
    for i in range(bits//shift):
        tmp = res ^ tmp >> shift
    return tmp

# right shift with mask inverse
def inverse_right_values(res,shift,mask,bits=32):
    tmp = res
    for i in range(bits//shift):
        tmp = res ^ tmp>>shift & mask
    return tmp

# left shift inverse
def inverse_left(res,shift,bits=32):
    tmp = res
    for i in range(bits//shift):
        tmp = res ^ tmp << shift
    return tmp

# left shift with mask inverse
def inverse_left_values(res,shift,mask,bits=32):
    tmp = res
    for i in range(bits//shift):
        tmp = res ^ tmp << shift & mask
    return tmp

def backtrace(cur):
    high = 0x80000000
    low = 0x7fffffff
    mask = 0x9908b0df
    state = cur
    for i in range(3,-1,-1):
        tmp = state[i+624]^state[i+397]
        # recover Y,tmp = Y
        if tmp & high == high:
            tmp ^= mask
            tmp <<= 1
            tmp |= 1
        else:
            tmp <<=1
        # recover highest bit
        res = tmp&high
        # recover other 31 bits,when i =0,it just use the method again it so beautiful!!!!
        tmp = state[i-1+624]^state[i+396]
        # recover Y,tmp = Y
        if tmp & high == high:
            tmp ^= mask
            tmp <<= 1
            tmp |= 1
        else:
            tmp <<=1
        res |= (tmp)&low
        state[i] = res
    return state

def recover_state(out):
    state = []
    for i in out:
        i = inverse_right(i,18)
        i = inverse_left_values(i,15,0xefc60000)
        i = inverse_left_values(i,7,0x9d2c5680)
        i = inverse_right(i,11)
        state.append(i)
    return state

f = open(r"F:\download\CTF\Backtrace_4259fa17d188c2ecdb898028c2f2df6e\output.txt","r").readlines()
c = []
for i in range(1000):
    c.append(int(f[i].strip()))

partS = recover_state(c)
state = backtrace([0]*4+partS)[:624]
# print(state)
prng = Random()
prng.setstate((3,tuple(state+[0]),None))
flag = "flag{" + ''.join(str(prng.getrandbits(32)) for _ in range(4)) + "}"
print(flag)

# 预测接下来的N个随机数
prng = Random()
prng.setstate((3,tuple(state+[0]),None))

# 预测flag的4个随机数
flag_randoms = [str(prng.getrandbits(32)) for _ in range(4)]
flag = "flag{" + ''.join(flag_randoms) + "}"
print(flag)

# 继续预测更多随机数（比如预测接下来的10个）
print("\n接下来的随机数:")
for i in range(10):
    print(f"随机数 {i+1}: {prng.getrandbits(32)}")
