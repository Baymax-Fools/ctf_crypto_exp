from Crypto.Util.number import long_to_bytes
import time, subprocess, re

N = 22187897828066510143339423882109101247209576020622451563694769495061581497972608742852704623563876205804618112075107327156665212714239515814760701261302340013984847109155166656629490882787990272673673984541861811022094404554774921448726355401410516219793271817030534522963962958070490308209942404568337176872647408723480204530638051188911383907146464459732256966570622985812410658915066458492530664670191920078132385328506090992831038029631657950434160340950576737109430430853406059464503283567537018385968948133588117647661573793901823708129071610152613927334203244932810281755256034938386141530974842254844569528321
p_high = 12893584713798331116600942759943150206120418151997023509455506536023696211103495532459701141560222506396287404281991806673169215725569387084632139466532811869

hidden_p_bits = 502

print("N.nbits() =", N.nbits())

def flatter_LLL(M):
    z = "[[" + "]\n[".join(" ".join(map(str, row)) for row in M) + "]]"
    ret = subprocess.check_output(["flatter"], input=z.encode())
    nums = list(map(int, re.findall(rb"-?\d+", ret)))
    return matrix(ZZ, M.nrows(), M.ncols(), nums)

# ============ 手写 Coppersmith (Howgrave-Graham)，格约化用 flatter ============
def coppersmith_hgg(pol, modulus, XX, mm, tt, use_flatter=True):
    dd = pol.degree()
    nn = dd * mm + tt

    polZ = pol.change_ring(ZZ)
    x = polZ.parent().gen()

    gg = []
    for jj in range(mm):
        for ii in range(dd):
            xshift = x**ii * modulus**(mm - jj) * polZ**jj
            gg.append(xshift)
    for ii in range(tt):
        xshift = x**ii * polZ**mm
        gg.append(xshift)

    gg.sort(key=lambda p: p.degree())

    BB = Matrix(ZZ, nn, nn)
    for ii in range(nn):
        for jj in range(ii + 1):
            BB[ii, jj] = gg[ii][jj] * XX**jj

    print(f"    [*] LLL on {nn}x{nn} matrix ...")
    t0 = time.time()
    if use_flatter:
        try:
            BB = flatter_LLL(BB)
        except Exception as e:
            print("    [!] flatter failed, fallback to native LLL:", e)
            BB = BB.LLL()
    else:
        BB = BB.LLL()
    print(f"    [*] LLL done in {time.time()-t0:.1f}s")

    # 用约化后第一行重建多项式，求根
    new_pol = 0
    for ii in range(nn):
        new_pol += x**ii * (BB[0, ii] / XX**ii)

    new_pol = new_pol.change_ring(QQ)
    roots = new_pol.roots(ring=ZZ)
    return [r[0] for r in roots]

# ============ 用它恢复 p ============
R.<x> = PolynomialRing(Zmod(N))
f = (x + p_high * 2^hidden_p_bits).monic()

X = 2^(hidden_p_bits + 1)

p_found = None
for m in [20, 30, 40, 50, 55, 60, 65, 70]:
    t = m
    print(f"[*] trying m={m}, t={t} ...")
    try:
        roots = coppersmith_hgg(f, N, X, m, t)
    except Exception as e:
        print("    error:", e)
        continue
    print(f"    roots={roots}")
    for r in roots:
        p_candidate = Integer(p_high * 2^hidden_p_bits + r)
        if p_candidate > 0 and N % p_candidate == 0:
            p_found = p_candidate
            print(f"[+] p found at m={m}")
            break
    if p_found:
        break

if p_found is None:
    raise RuntimeError("仍未找到 p，需要继续加大 m")

p = p_found
q = N // p
assert p * q == N
print(f"p = {p}")
print(f"q = {q}")