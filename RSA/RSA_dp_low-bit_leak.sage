from Crypto.Util.number import *
from sage.all import *

n = 0xd7152506aa9cec05e5335d6b46f5491407c3199fd51091f1f6030d3762b9e03f49c9dcdc075054e0cc148b974b41854bd93b4ee16a2a876ee62005e80ef806b7aa3b64b1bf9b1fa773e353d0cdb9ff9783ddd5f5e67499ad10f361e938d00b82a6a4c42a0535c5e76721798e86b45cd4b8d03b0d7e75c2be8766a1e843bdc641
e = 0x10001
dq_l = 0xc90bcecf1cbab3358585e8a041d1b1
q_inv_p = 0xe3016cb3609c1d643c167439c3b938b881f4237f24860d3b1cb85a626d5ccd4726964e0f8270d6c4df9ebfebcc538e4ee5e1a7b7368ede51ec6ae917f78eb598
c = 30867633715813868869594516898484466949832562855682390289015078636128522331216753026144388726648565996116979180534633656943032219373784742974695394149452376092090200793002116674808387426569939440254310919848751355794417768901965964656988835770326844588984815500667657575205646452291264006781430216086103523765

nbits = n.nbits()
konw_bits = dq_l.nbits()
mod = 2**konw_bits
P.<x> = PolynomialRing(Zmod(n))

print("Start solving...")

for k in range(1, e + 1):
    if k % 2 == 0: 
        continue

    q_l = ((e * dq_l - 1) * inverse_mod(k, mod) + 1) % mod

    # 构造二次多项式
    f = q_inv_p * (x * mod + q_l)**2 - (x * mod + q_l)
    f = f.monic()

    roots = f.small_roots(X=2**(nbits // 2 - konw_bits + 1), beta=1)

    if roots:
        x_val = int(roots[0])
        q = x_val * mod + q_l
        if n % q == 0:
            print(f"[*] Found q with k = {k}")
            p = n // q
            d = inverse_mod(e, (p-1)*(q-1))
            m = pow(c, d, n)
            print("Message:", long_to_bytes(int(m)))
            break
# b'flag{the_broken_pem_is_dangerous!}'
