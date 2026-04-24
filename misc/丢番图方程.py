from Crypto.Util.number import isPrime
import gmpy2

def find_primes_from_diophantine(a, b, c, p_bits, q_bits, search_range=2000):
    """
    从丢番图方程 a*p + b*q = c 中寻找特定比特长度的素数p和q
    """
    g = gmpy2.gcd(a, b)
    if c % g != 0:
        print("方程无整数解")
        return None

    gcd_val, x0, y0 = gmpy2.gcdext(a, b)
    mult = c // g
    p0 = mult * x0
    q0 = mult * y0

    a_div_g = a // g
    b_div_g = b // g

    target_p = 2 ** (p_bits - 1)
    if b_div_g != 0:
        m_approx = (target_p - p0) // b_div_g
    else:
        m_approx = 0

    for delta in range(-search_range, search_range + 1):
        m = m_approx + delta
        p_candidate = p0 + m * b_div_g
        q_candidate = q0 - m * a_div_g

        if (p_candidate > 0 and q_candidate > 0 and
                p_candidate.bit_length() == p_bits and
                q_candidate.bit_length() == q_bits and
                isPrime(p_candidate) and isPrime(q_candidate) and
                a * p_candidate + b * q_candidate == c):
            return p_candidate, q_candidate

    return None

# 解决原始问题（需要先确定t）
def solve_original():
    leak = -22224149994648923268789165509278165317007019455022228125461360264793582171180635864579051464573337703687603580778495942125972142098772460556824154925867963032811028915392488366933631534188006255843741792247909707811296603266184677505976551213494692490958051692640473222958630333160094121388820523562777011757770463239266929437423460046580341706128217879344508078081919107
    r = 3713559774641553436276209941711693805945428824832652977855633547840173231986353608653241781778848123547004971784830459033920945156217927983674366335721583894756256542949490248528661744237220067
    s = 3253961557665053735006933248952708348480142618850029234835814776973317490037893238569932660577366140882645494681486024928968833274980657993492577660282073430006337665469597700457553957032764444206539094923833498222709

    # 枚举t (15位素数)
    for t in range(2 ** 14, 2 ** 15):
        if isPrime(t):
            # 方程: r*p - s*q = leak - t
            result = find_primes_from_diophantine(
                a=r, b=-s, c=leak - t,
                p_bits=512, q_bits=512
            )
            if result:
                p, q = result
                print(f"找到解: t={t}")
                print(f"p = {p}")
                print(f"q = {q}")
                return p, q, t

    print("未找到解")
    return None

# 使用
if __name__ == "__main__":
    p, q, t = solve_original()