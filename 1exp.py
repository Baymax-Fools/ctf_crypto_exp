from z3 import *  
  
p, q = Ints('p q')  
s = Solver()  
s.add(p * q == pq)  
s.add(pq * 2 ** 240 * 10 ** (79) + p ** 2 * 2 ** 120 * 10 ** 39 + q ** 2 * 2 ** 120 * 10 ** 40 + pq == n)  
s.check()  
model = s.model()  
p = model[p].as_long()  
q = model[q].as_long()  
print(p,q)