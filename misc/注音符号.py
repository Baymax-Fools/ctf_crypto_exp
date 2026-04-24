a = "A	B	C	D	E	F	G	H	I	J	K	L	M	N	O	P	Q	R	S	T	U	V	W	X	Y	Z	1	2	3	4	5	6	7	8	9	0	-	;	,	.	/"
b = "ㄇ	ㄖ	ㄏ	ㄎ	ㄍ	ㄑ	ㄕ	ㄘ	ㄛ	ㄨ	ㄜ	ㄠ	ㄩ	ㄙ	ㄟ	ㄣ	ㄆ	ㄐ	ㄋ	ㄔ	ㄧ	ㄒ	ㄊ	ㄌ	ㄗ	ㄈ	ㄅ	ㄉ	ˇ	ˋ	ㄓ	ˊ	˙	ㄚ	ㄞ	ㄢ	ㄦ	ㄤ	ㄝ	ㄡ	ㄥ"

a = a.split('\t')
b = b.split('\t')
cvt = {x : y for x, y in zip(a, b)}

with open(r'F:\download\CTF\wtf\wtf.txt', 'r', encoding='utf-8') as f:
    s = f.read()

t = ''.join(cvt[x] if x in cvt else x for x in s)

print(t)