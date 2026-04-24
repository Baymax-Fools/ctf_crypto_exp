import hashlib

demo = 'flag{www_shiyanbar_com_is_very_good_'
check = '38e4c352809e150186920aac37190cbc'

for i in range(32, 126):
    for j in range(32, 126):
        for k in range(32, 126):
            for m in range(32, 126):
                tmp = demo + chr(i) + chr(j) + chr(k) + chr(m) + '}'
                hash = hashlib.md5(tmp.encode('utf8')).hexdigest()
                if check == hash:
                    print(tmp)
                    exit()

