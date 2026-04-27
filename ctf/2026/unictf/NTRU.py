from Crypto.Util.number import long_to_bytes
N = 31
p = 257
q = 12289
h_list = [9603, 11838, 1242, 5868, 12249, 3130, 3722, 5910, 5879, 7672, 1119, 339, 10748, 7310, 6370, 9353, 10589, 10739, 10213, 2560, 5132, 4889, 11292, 2649, 2556, 8037, 3146, 9533, 11563, 1554, 304]
c_list = [91, 11459, 932, 4345, 12153, 9504, 5147, 7268, 2493, 8891, 8712, 5785, 11608, 7683, 11327, 8453, 10380, 6004, 7849, 1622, 6154, 10369, 10278, 769, 11676, 11492, 4564, 5445, 10909, 11502, 12216]

def circulant(v):
    return Matrix(ZZ, [v[-i:] + v[:-i] for i in range(len(v))])

H = circulant(h_list)

#print(h_list)
#print(H)

c_row = matrix(ZZ, 1, N, c_list)
I = identity_matrix(ZZ, N)
Q = q * identity_matrix(ZZ, N)

B = block_matrix([
    [c_row,0,1000],
    [-H,1000*I,0],
    [Q,0,0]])

B_lll = B.LLL()

for i in B_lll:
    if abs(i[-1]) == 1000:
        if i[-1] == -1000:
            i = -i
        m = ""
        for j in i[:31]:
            m += chr(j % q)
        print(m)
