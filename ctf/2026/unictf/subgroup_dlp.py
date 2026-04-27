import sys
from Crypto.Util.number import long_to_bytes
 
n = 20416580311348568104958456290409800602076453150746674606637172527592736894552749500299570715851384304673805100612931000268540860237227126141075427447627491168
c = 8195229101228793312160531614487746122056220479081491148455134171051226604632289610379779462628287749120056961207013231802759766535835599450864667728106141697
g = 7
 
factors_list = [
    (2, 5),
    (3, 2),
    (10711086940911733573, 1),
    (188455199626845780197, 3), 
    (988854958862525695246052320176260067587096611000882853771819829938377275059, 1)
]

def solve_pe(g,c,p,e):
    print(f"solve {g}^{e} mod {p} :")
    F = GF(p)
    x0 = discrete_log(F(c),F(g))
    
    current_x = x0
    
    full_mod = p**e
    g_pow_p_minus_1 = power_mod(g,p-1,full_mod)
    
    for i in range(1,e):
        print(f"mod p^{i + 1}")
        mod_next = p**(i+1)

        g_x = power_mod(g,current_x,mod_next) # g^x_0 mod p^mod_next
        
        rem = (c * inverse_mod(g_x,mod_next)) % mod_next
        
        val_numerator = (rem -1) // (p**i)
        val_deniminator = (g_pow_p_minus_1 - 1) // p
        
        k = (val_numerator * inverse_mod(val_deniminator,p)) % p
        
        current_x = current_x + k * (p-1) * (p**(i-1))
    
    return current_x

dlogs = []
moduli = []
 
print("[*] Starting Optimized DLP with Correct Order Calculation...")
 
for p, e in factors_list:
    pe = p ** e
    print(f"n[*] Processing factor: {p}^{e}")
 
    real_order_p = GF(p)(g).multiplicative_order()
    real_full_order = real_order_p * (p**(e-1))
    print(f"    [-] Real Order: {real_full_order}")
 
    if e > 1 and p > 10000:
        try:
            x = solve_pe(g, c, p, e)
            dlogs.append(x)
            moduli.append(real_full_order)
            print(f"    [+] Solved! x = {x}")
        except Exception as err:
             print(f"    [!] Lifting failed: {err}")
    else:
        R = Zmod(pe)
        g_sub = R(g)
        c_sub = R(c)
        x = discrete_log(c_sub, g_sub)
        dlogs.append(x)
        moduli.append(real_full_order)
        print(f"    [+] Solved! x = {x}")
 
print("n[*] Reconstructing m with CRT...")
try:
    m = crt(dlogs, moduli)
    print(f"[+] Recovered m: {m}")
 
    flag = long_to_bytes(int(m))
    print(f"n[SUCCESS] FLAG: {flag.decode()}")
except Exception as e:
    print(f"[!] CRT Failed: {e}")
    print("Dlogs:", dlogs)
    print("Moduli:", moduli)
    
    

'''
from Crypto.Util.number import *
 
flag = b'UniCTF{???}'
m = bytes_to_long(flag)
n = 20416580311348568104958456290409800602076453150746674606637172527592736894552749500299570715851384304673805100612931000268540860237227126141075427447627491168
print(pow(7,m,n))
# c = 8195229101228793312160531614487746122056220479081491148455134171051226604632289610379779462628287749120056961207013231802759766535835599450864667728106141697
'''