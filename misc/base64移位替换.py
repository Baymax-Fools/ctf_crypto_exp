import base64

s= '3EP/3VNFFmNEAnlHD5dCMmVHD5ad9uG'
a = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/='  #base64编码表
flag = ''
for i in s:
    flag += a[(a.index(i)-30)%64]
if len(flag)%4!=0:
    flag += '='*(4-len(flag)%4)
print(flag)
print(base64.b64decode(flag).decode('UTF-8'))
#ZmxhZ3vnnIvmiJHplb/kuI3plb8/fQo=
#flag{看我长不长?}