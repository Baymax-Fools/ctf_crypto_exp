import hashlib

s = "11786190273906782566706300546504742629011900435269701041731697414027484824601255112180676531145294320443777235338538357924760601782873554458995940394745073"
md5 = hashlib.md5()
md5.update(s.encode())
m_hex = md5.hexdigest()
print(m_hex)
print(len(m_hex))
# m = ""
# for i in range(0,len(m_hex),2):
#     m += m_hex[i]
# print(m)
#
# for i in range(65,91):
#     for j in range(65,91):
#         for k in range(65,91):
#             for y in range(65,91):
#                 for z in range(65,91):
#                     for p in range(65, 91):
#                         m=hashlib.md5()
#                         m.update(chr(i).encode()+ chr(j).encode()+ chr(k).encode() + chr(y).encode()+ chr(z).encode()+ chr(p).encode())
#                         des=m.hexdigest()
#                         if des[-6:] == '8b184b':
#                             print(chr(i)+chr(j)+chr(k)+chr(y) + chr(z) + chr(p))
#                             print(des)