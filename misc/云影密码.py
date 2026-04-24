a="44414440122401244401404424404421440414"
s=a.split('0')
print(s)
l=[]
for i in s:
    sum=0
    for j in i:
        sum+=eval(j)
    l.append(chr(sum+64))
print(''.join(l))
