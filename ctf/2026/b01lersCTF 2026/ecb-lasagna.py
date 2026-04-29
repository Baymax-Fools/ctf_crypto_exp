#!/usr/bin/env python3
"""
============================================================
b01lersCTF 2026 - "too many tags" 攻击脚本（完整注释版）
============================================================

【攻击目标】
服务器使用同一个 32 字节随机密钥作为:
  1. AES-GCM 的加密密钥
  2. Python random.Random (MT19937) 的种子

服务器提供了一个"oracle"（查询接口）：
  - 每次查询返回一个单块密文 C 和一个被"污染"的标签 T
  - 标签的低 64 位被替换为：low64(GHASH(H, C)) XOR fault_value
  - 其中 fault_value = (out0 << 32) | out1，out0/out1 是 MT19937 的连续两个 32 位输出
  - 总共有 704 次查询机会

flag 以标准 AES-GCM（正确标签）加密，并在开始时打印。

【攻击策略】
1. 收集所有 704 个查询的 (密文, 污染标签)
2. 利用 GHASH 和 MT19937 在 GF(2) 上的线性性质，建立一个包含 20096 个未知数的线性方程组
   - 未知数: H (128 bits) + MT 状态 (624 × 32 = 19968 bits)
   - 每个查询提供 64 个方程（标签低 64 位）
   - 总共: 704 × 64 = 45056 个方程 >> 20096 个未知数
3. 用高斯消元法求解，恢复 H 和 MT19937 的完整状态
4. 用 Z3 逆向 Python 的 seed() 过程，从 MT 状态反推出种子
5. 种子就是 32 字节的 AES 密钥，用标准 AES-GCM 解密 flag
"""

import re
import random
from typing import Dict, List, Tuple

from pwn import remote
from z3 import BitVec, BitVecVal, LShR, Solver, sat
from cryptography.hazmat.primitives.ciphers.aead import AESGCM


# ============================================================
# 常量定义
# ============================================================
BLOCK_SIZE = 16                    # AES 块大小：16 字节
MASK64 = (1 << 64) - 1            # 64 位掩码（低 64 位全 1）
MASK128 = (1 << 128) - 1          # 128 位掩码
GCM_REDUCTION = 0xE1000000000000000000000000000000  # GCM 的 GF(2^128) 约化多项式

# MT19937 的常量
N = 624           # MT 状态大小：624 个 32 位整数
M = 397           # MT 算法参数
MATRIX_A = 0x9908B0DF  # MT 的矩阵 A
WORD_MASK = 0xFFFFFFFF  # 32 位掩码

QUERY_BUDGET = 704  # 可查询次数上限

# 未知数统计：
#   H: 128 bits (GCM 的 hash 子密钥)
#   MT seeded-state: 624 × 32 bits
H_BITS = 128
MT_BITS = 624 * 32
TOTAL_BITS = H_BITS + MT_BITS  # = 20096 个 GF(2) 未知数


# ============================================================
# GF(2^128) 上的 GHASH 计算
# ============================================================
def gf_mul(x: int, y: int) -> int:
    """
    GF(2^128) 域上的乘法（逐位算法）
    GCM 用此来定义 GHASH 的乘法操作
    """
    z = 0
    v = x
    for i in range(128):
        # 如果 y 的当前位（从最高位往下检查）是 1
        if (y >> (127 - i)) & 1:
            z ^= v          # 累加 v
        # v 除以 x（带约化多项式）：右移一位，若最低位为 1 则异或约化多项式
        if v & 1:
            v = (v >> 1) ^ GCM_REDUCTION
        else:
            v >>= 1
    return z & MASK128


def length_block_for_one_block_message() -> int:
    """
    构造 GCM 的长度块: len(附加数据) || len(密文)
    附加数据长度为 0，密文长度为 16 字节 = 128 位
    所以: 0^64 || 128 = 0x00000000000000000000000000000080
    """
    return int.from_bytes(
        (0).to_bytes(8, "big") + (16 * 8).to_bytes(8, "big"), "big"
    )


LEN_BLOCK = length_block_for_one_block_message()  # 预计算的长度块


def ghash_low64_masks(cipher_block: int) -> List[int]:
    """
    【关键函数】计算 GHASH 低 64 位在 GF(2) 上的线性掩码

    对于单块密文 C，GHASH 计算公式为:
        GHASH(H, C) = C * H^2 ⊕ L * H    （在 GF(2^128) 上）

    这个函数返回 64 个掩码 mask[0..63]：
        对于 H 的第 j 个比特，如果它对 low64(GHASH) 的第 b 个比特有贡献，
        则 mask[b] 的第 j 位为 1。

    换句话说：
        bit_b(low64(GHASH)) = parity(mask[b] & H_bits)

    其中 H_bits 是 H 的 128 位按 LSB 排列（第 j 位 = H 的第 j 个比特）。

    为什么这样做？因为我们最终要建立一个 GF(2) 线性方程组，
    需要把 "GHASH 的低 64 位的每个比特" 表示为 "H 的 128 个比特" 的线性组合。
    """
    masks = [0] * 64
    for j in range(128):
        # basis: H 只有一个比特为 1（第 j 位）时的 H 值
        # 因为 GF(2^128) 上的运算是线性的，我们可以分别考虑每个比特的贡献
        basis = 1 << j

        # 计算当 H = basis 时的 GHASH 值
        # H^2 = gf_mul(basis, basis)，即 basis 的平方
        # C * H^2 = gf_mul(cipher_block, gf_mul(basis, basis))
        # L * H = gf_mul(LEN_BLOCK, basis)
        # 总 GHASH = C * H^2 ⊕ L * H
        val = gf_mul(cipher_block, gf_mul(basis, basis)) ^ gf_mul(LEN_BLOCK, basis)

        low = val & MASK64  # 取低 64 位

        # 对于低 64 位的每一个比特 b：
        # 如果该比特为 1，说明 basis (H 的第 j 位) 对 low64(GHASH) 的第 b 位有贡献
        for b in range(64):
            if (low >> b) & 1:
                masks[b] |= 1 << j  # 标记：H 的第 j 位影响 low64 的第 b 位

    return masks


# ============================================================
# MT19937 的符号化（GF(2) 线性）模型
#
# 核心思想：MT19937 的所有内部操作（异或、移位、与掩码、扭态）
# 在 GF(2) 上都是线性的！因为：
#   - XOR 是线性的
#   - 右移/左移是线性的
#   - 与常量掩码是线性的（每个输出比特是输入比特的线性组合）
#   - 扭态操作是线性的
#
# 我们把 MT 状态中的每一个比特表示为一个独立的未知数（GF(2) 变量），
# 然后追踪这些变量经过所有操作后的线性组合。
#
# 变量编号方式：
#   bit_var = 1 << (H_BITS + 32 * word_idx + bit_idx)
#   即用一个 20096 位整数中的某一位来表示一个 GF(2) 变量
# ============================================================

def mt_var(word_idx: int, bit_idx: int) -> int:
    """
    返回 MT 状态中第 word_idx 个字的第 bit_idx 个比特的 GF(2) 变量
    用位掩码表示：第 (128 + 32*word_idx + bit_idx) 位为 1
    """
    return 1 << (H_BITS + 32 * word_idx + bit_idx)


def make_word_from_mt_vars(word_idx: int) -> List[int]:
    """创建一个由 32 个 GF(2) 变量组成的"字"（长度为 32 的列表）"""
    return [mt_var(word_idx, b) for b in range(32)]


def xor_word(a: List[int], b: List[int]) -> List[int]:
    """两个字逐比特异或（在 GF(2) 中就是 XOR）"""
    return [x ^ y for x, y in zip(a, b)]


def shr_word(a: List[int], k: int) -> List[int]:
    """
    逻辑右移 k 位（MT 的 >> 操作）
    例如：shr_word([b0,b1,...,b31], 1) = [b1,b2,...,b31,0]
    这是线性的！
    """
    out = [0] * 32
    for i in range(32 - k):
        out[i] = a[i + k]
    # 高位补 0
    return out


def shl_word(a: List[int], k: int) -> List[int]:
    """
    左移 k 位（MT 的 << 操作）
    例如：shl_word([b0,b1,...,b31], 1) = [0,b0,b1,...,b30]
    这也是线性的！
    """
    out = [0] * 32
    for i in range(k, 32):
        out[i] = a[i - k]
    return out


def and_mask_word(a: List[int], mask: int) -> List[int]:
    """
    与常量掩码做按位与（MT 的 & 操作）
    如果 mask 的某位是 0，输出该位为 0
    如果 mask 的某位是 1，输出该位 = 输入该位
    这仍然是线性的（乘以 0 或 1）！
    """
    return [a[i] if ((mask >> i) & 1) else 0 for i in range(32)]


def temper_word(x: List[int]) -> List[int]:
    """
    MT19937 的 tempering 变换（将状态字转化为输出）
    
    CPython 的实现:
        y = x
        y ^= (y >> 11)
        y ^= (y << 7) & 0x9D2C5680
        y ^= (y << 15) & 0xEFC60000
        y ^= (y >> 18)
    
    所有操作在 GF(2) 上都是线性的！
    """
    y = x[:]
    y = xor_word(y, shr_word(y, 11))          # y ^= (y >> 11)
    y = xor_word(y, and_mask_word(shl_word(y, 7), 0x9D2C5680))   # y ^= (y << 7) & 0x9D2C5680
    y = xor_word(y, and_mask_word(shl_word(y, 15), 0xEFC60000))  # y ^= (y << 15) & 0xEFC60000
    y = xor_word(y, shr_word(y, 18))          # y ^= (y >> 18)
    return y


def twist_state(state: List[List[int]]) -> List[List[int]]:
    """
    MT19937 的完整扭态（twist）操作
    
    这是 MT 的核心状态更新：当 index 达到 N=624 时，
    将 624 个字的状态进行一次完整的扭态变换。
    
    与 CPython 的 random.py 实现完全一致。
    所有操作在 GF(2) 上都是线性的！
    """
    st = [w[:] for w in state]  # 深拷贝状态

    # 第一阶段：kk 从 0 到 226 (N-M-1 = 624-397-1)
    for kk in range(N - M):
        # y = 状态[kk] 的最高位 + 状态[kk+1] 的低 31 位
        y = [0] * 32
        for b in range(31):
            y[b] = st[kk + 1][b]        # st[kk+1] 的低 31 位
        y[31] = st[kk][31]              # st[kk] 的最高位

        # yA = y >> 1（即除以 2 然后根据最低位决定是否异或 MATRIX_A）
        yA = shr_word(y, 1)
        low = y[0]
        for b in range(32):
            if (MATRIX_A >> b) & 1:
                yA[b] ^= low           # 如果 y 的最低位为 1，异或 MATRIX_A

        st[kk] = xor_word(st[kk + M], yA)  # st[kk] = st[kk+397] ^ yA

    # 第二阶段：kk 从 227 到 622
    for kk in range(N - M, N - 1):
        y = [0] * 32
        for b in range(31):
            y[b] = st[kk + 1][b]
        y[31] = st[kk][31]

        yA = shr_word(y, 1)
        low = y[0]
        for b in range(32):
            if (MATRIX_A >> b) & 1:
                yA[b] ^= low

        st[kk] = xor_word(st[kk + (M - N)], yA)  # st[kk] = st[kk+397-624] ^ yA

    # 第三阶段：处理最后一个字 kk = 623
    y = [0] * 32
    for b in range(31):
        y[b] = st[0][b]                  # st[0] 的低 31 位
    y[31] = st[N - 1][31]               # st[623] 的最高位

    yA = shr_word(y, 1)
    low = y[0]
    for b in range(32):
        if (MATRIX_A >> b) & 1:
            yA[b] ^= low

    st[N - 1] = xor_word(st[M - 1], yA)  # st[623] = st[396] ^ yA

    return st


class SymbolicMT:
    """
    符号化的 MT19937 —— 所有状态比特都是 GF(2) 变量
    
    模拟从 seed 后的第一个 getrandbits(32) 调用开始的输出。
    Python 在 seed() 后设置 self.index = 624，
    所以第一次 getrandbits(32) 会先触发 twist。
    """
    def __init__(self):
        # 初始状态：624 个字，每个字 32 个 GF(2) 变量
        self.state = [make_word_from_mt_vars(i) for i in range(N)]
        self.index = N  # 关键！Python 在 seed() 后设置 index = 624

    def getrandbits32_symbolic(self) -> List[int]:
        """
        获取下一个 32 位随机数的符号表示（GF(2) 变量的线性组合）
        
        与 CPython 行为一致：
        1. 如果 index >= 624，先做 twist
        2. 取 state[index] 做 tempering
        3. index++
        """
        if self.index >= N:
            self.state = twist_state(self.state)  # 扭态！
            self.index = 0
        y = temper_word(self.state[self.index])   # 对状态字做 tempering
        self.index += 1
        return y


# ============================================================
# GF(2) 线性方程组求解器（高斯消元法）
#
# 每个方程: row_1*x_1 ⊕ row_2*x_2 ⊕ ... ⊕ row_n*x_n = rhs
# 其中 row 是一个整数，其二进制表示标记了哪些变量参与这个方程
# ============================================================
class GF2Solver:
    """GF(2) 上的高斯消元求解器"""

    def __init__(self, nvars: int):
        self.nvars = nvars
        self.pivots: Dict[int, Tuple[int, int]] = {}
        # pivots[p] = (row, rhs)
        # p 是主元的位置（最高位），row 是该方程各位的系数，rhs 是等式右边

    def add_equation(self, row: int, rhs: int):
        """
        添加一个 GF(2) 方程：parity(row & X) = rhs
        其中 row 的二进制第 i 位表示变量 x_i 的系数（0 或 1）
        """
        x = row
        y = rhs & 1  # rhs 只取最低位（在 GF(2) 中）

        # 用已有的主元消去 x 中的已知变量
        while x:
            p = x.bit_length() - 1  # x 的最高位位置
            if p in self.pivots:
                prow, prhs = self.pivots[p]
                x ^= prow    # 消去第 p 位
                y ^= prhs    # 相应地调整右边
            else:
                # 找到了一个新的主元
                self.pivots[p] = (x, y)
                return

        # 如果 x 消为 0 但 y ≠ 0，说明方程矛盾
        if y:
            raise ValueError("Inconsistent linear system")
        # 否则是冗余方程（可由已有方程推出），忽略

    def solve(self) -> List[int]:
        """
        回代求解，返回每个变量的值（0 或 1）
        从低位到高位依次求解
        """
        sol = [0] * self.nvars
        packed = 0  # 已求解变量的打包值

        # 必须从低位到高位求解（因为高位可能依赖低位）
        for p in sorted(self.pivots.keys()):
            row, rhs = self.pivots[p]
            # row 中第 p 位是主元（系数为 1），其余位是与其他变量的关系
            rest = row ^ (1 << p)  # 去掉主元位
            # 利用已求解的变量计算
            bit = rhs ^ ((rest & packed).bit_count() & 1)
            #      rhs  XOR  (已求解变量对结果的贡献)
            sol[p] = bit
            if bit:
                packed |= 1 << p

        return sol

    def check_solution(self, sol: List[int]) -> bool:
        """验证解是否满足所有方程"""
        packed = 0
        for i, b in enumerate(sol):
            if b:
                packed |= 1 << i
        for _, (row, rhs) in self.pivots.items():
            if ((row & packed).bit_count() & 1) != rhs:
                return False
        return True


# ============================================================
# 远程 IO 交互
# ============================================================
def recv_menu(io) -> bytes:
    """接收菜单提示"""
    return io.recvuntil(b"> ")


def parse_initial(blob: bytes):
    """解析服务器启动时发送的数据：flag 的 nonce、密文、标签、查询预算"""
    s = blob.decode()
    flag_nonce = bytes.fromhex(re.search(r"flag_nonce = ([0-9a-f]+)", s).group(1))
    flag_ct = bytes.fromhex(re.search(r"flag_ciphertext = ([0-9a-f]+)", s).group(1))
    flag_tag = bytes.fromhex(re.search(r"flag_tag = ([0-9a-f]+)", s).group(1))
    budget = int(re.search(r"query budget = (\d+)", s).group(1))
    return flag_nonce, flag_ct, flag_tag, budget


def collect_all_queries_fast(io, n=QUERY_BUDGET):
    """
    一次性发送所有查询请求（选 n 次 "1"，然后选 "2" 退出）
    然后解析所有返回的 (密文, 污染标签)
    
    这比逐个查询快得多，因为网络延迟被摊销了。
    """
    io.send(b"1\n" * n + b"2\n")
    data = io.recvall(timeout=20).decode()

    matches = re.findall(
        r"nonce = ([0-9a-f]+)\n"
        r"ciphertext = ([0-9a-f]+)\n"
        r"tag = ([0-9a-f]+)\n"
        r"queries_left = (\d+)",
        data,
    )

    if len(matches) != n:
        raise RuntimeError(f"expected {n} queries, got {len(matches)}")

    queries = []
    for _nonce_hex, ct_hex, tag_hex, _left in matches:
        queries.append((bytes.fromhex(ct_hex), bytes.fromhex(tag_hex)))

    return queries


# ============================================================
# 核心攻击：恢复 H 和 MT19937 的种子状态
# ============================================================
def recover_h_and_mt_state(queries: List[Tuple[bytes, bytes]]) -> Tuple[int, List[int]]:
    """
    从所有查询中恢复 H (GCM hash 子密钥) 和 MT19937 的完整状态
    
    对于每个查询 (C, T):
      - 已知：密文 C 和污染标签 T
      - T 的低 64 位 = low64(GHASH(H, C)) XOR fault_value
      - fault_value = (out0 << 32) | out1 （两个 MT 输出）
      
    这给出了 64 个 GF(2) 方程（每个比特一个）。
    704 个查询 × 64 = 45056 个方程 >> 20096 个未知数。
    """
    solver = GF2Solver(TOTAL_BITS)
    smt = SymbolicMT()  # 符号化的 MT19937

    for idx, (ct, tag) in enumerate(queries):
        c = int.from_bytes(ct, "big")
        # 获取该密文对应的 GHASH 低 64 位的 64 个线性掩码
        g_masks = ghash_low64_masks(c)

        # 获取这个查询对应的两个 MT 输出的符号表示
        out0 = smt.getrandbits32_symbolic()  # fault_value 的高 32 位
        out1 = smt.getrandbits32_symbolic()  # fault_value 的低 32 位

        low = int.from_bytes(tag, "big") & MASK64  # 污染标签的低 64 位

        for b in range(64):
            # 我们从服务器收到的标签低 64 位:
            #   tag_low = low64(GHASH(H, C)) XOR fault_value
            #
            # 所以对于第 b 个比特:
            #   tag_low[b] = GHASH_low[b] ⊕ fault_value[b]
            #
            # 即: GHASH_low[b] ⊕ fault_value[b] = tag_low[b]
            # 这是一个 GF(2) 方程！
            
            row = g_masks[b]  # H 的各位对 GHASH_low[b] 的贡献

            # fault_value = (out0 << 32) | out1
            # 按 LSB 索引：
            #   低 32 位 (bit 0..31)   → out1[0..31]
            #   高 32 位 (bit 32..63)  → out0[0..31]
            if b < 32:
                row ^= out1[b]     # 加上 fault_value 的低 32 位对第 b 位的贡献
            else:
                row ^= out0[b - 32]  # 加上 fault_value 的高 32 位对第 b 位的贡献

            rhs = (low >> b) & 1   # 右边 = 污染标签的第 b 位
            solver.add_equation(row, rhs)

        if (idx + 1) % 64 == 0:
            print(f"[+] processed {idx + 1}/{len(queries)} queries")

    # CPython 的 seed() 后不变式：mt[0] = 0x80000000
    # Python 在 seed() 之后会把 mt[0] 强制设置为 0x80000000
    for b in range(32):
        solver.add_equation(mt_var(0, b), (0x80000000 >> b) & 1)

    print("[+] solving linear system...")
    sol = solver.solve()
    assert solver.check_solution(sol), "linear solution does not satisfy the system"

    # 从前 128 位提取 H
    H = 0
    for j in range(128):
        if sol[j]:
            H |= 1 << j

    # 从后续位提取 MT 状态（624 个字，每个 32 位，按 LSB 排列）
    mt_state = []
    base = H_BITS
    for i in range(624):
        x = 0
        for b in range(32):
            if sol[base + 32 * i + b]:
                x |= 1 << b
        mt_state.append(x)

    return H, mt_state


def check_mt_state_recovery(mt_state: List[int], queries: List[Tuple[bytes, bytes]], H: int, count: int = 8):
    """
    验证恢复的 MT 状态和 H 是否正确
    用恢复的状态模拟 MT19937，重新计算前几个查询的标签，对比是否匹配
    """
    r = random.Random()
    r.setstate((3, tuple(mt_state + [624]), None))  # 恢复 MT 状态

    ok_all = True
    for i, (ct, tag) in enumerate(queries[:count]):
        out0 = r.getrandbits(32)
        out1 = r.getrandbits(32)
        fault = ((out0 << 32) | out1) & MASK64

        c = int.from_bytes(ct, "big")
        # 重新计算 GHASH = C * H^2 ⊕ L * H
        ghash = gf_mul(c, gf_mul(H, H)) ^ gf_mul(LEN_BLOCK, H)
        expected = (ghash ^ fault) & MASK64
        actual = int.from_bytes(tag, "big") & MASK64
        ok = expected == actual
        ok_all &= ok
        print(f"[chk] {i}: expected={expected:016x} actual={actual:016x} ok={ok}")

    if not ok_all:
        raise RuntimeError("MT/H sanity check failed")
    print("[+] MT/H recovery verified!")


# ============================================================
# 用 Z3 逆向 Python 的 seed() 过程，从 MT 状态恢复种子
#
# 这是攻击的最后一步：我们有了 MT19937 在 seed() 后的完整状态，
# 需要反推出调用 random.Random(seed_int) 时的 seed_int。
#
# Python 的种子初始化分为几个阶段：
# 1. init_genrand(19650218) — 用固定种子 19650218 初始化
# 2. init_by_array(key, len(key)) — 用种子字节数组"搅拌"
# 3. mt[0] = 0x80000000 — 强制设置第一个字
#
# 关键：如果 key 只有 8 个字或更少（即种子 ≤ 256 bits），
# init_by_array 是可逆的，可以用 Z3 求解。
# ============================================================

def init_genrand_19650218() -> List[int]:
    """
    用 CPython 的固定种子 19650218 初始化 MT 状态
    这是 Python seed() 的第一阶段
    """
    mt = [0] * N
    mt[0] = 19650218
    for i in range(1, N):
        mt[i] = (1812433253 * (mt[i - 1] ^ (mt[i - 1] >> 30)) + i) & WORD_MASK
    return mt


INIT_19650218 = init_genrand_19650218()  # 预计算


def python_state_from_seed_words(words_le: List[int]) -> List[int]:
    """
    用给定的种子字（little-endian 32 位）正向创建 MT 状态
    用于验证 Z3 找到的候选种子是否正确
    """
    seed_int = 0
    for i, w in enumerate(words_le):
        seed_int |= (w & WORD_MASK) << (32 * i)
    r = random.Random(seed_int)
    return list(r.getstate()[1][:-1])  # 去掉 index，只保留 624 个字的状态


def recover_seed_words_with_z3(target_state: List[int], max_words: int = 8) -> List[int]:
    """
    用 Z3 逆向 init_by_array，从目标 MT 状态反推出种子字
    
    Python 的 init_by_array 将种子字节数组（每 4 字节 = 1 个字）混入 MT 状态。
    因为我们的 master_key 是 32 字节，最多 8 个 32 位字，
    尝试 key_words = 1..8。
    """
    print("[+] recovering seed words with z3...")

    for key_words in range(1, max_words + 1):
        print(f"[+] trying key_words = {key_words}")

        # 创建 key_words 个 Z3 符号变量（32 位）
        key = [BitVec(f"k_{key_words}_{i}", 32) for i in range(key_words)]
        
        # 从固定种子 19650218 的初始状态开始
        mt = [BitVecVal(x, 32) for x in INIT_19650218]

        i = 1  # mt 索引从 1 开始
        j = 0  # key 索引
        k = max(N, key_words)  # 循环次数 = max(624, key_words)

        # init_by_array 第一阶段
        for _ in range(k):
            mt[i] = (
                mt[i]
                ^ ((mt[i - 1] ^ LShR(mt[i - 1], 30)) * BitVecVal(1664525, 32))
            ) + key[j] + BitVecVal(j, 32)
            # mt[i] ^= (mt[i-1] ^ (mt[i-1] >> 30)) * 1664525
            # mt[i] += key[j] + j

            i += 1
            j += 1

            if i >= N:
                mt[0] = mt[N - 1]  # 循环
                i = 1
            if j >= key_words:
                j = 0

        # init_by_array 第二阶段
        for _ in range(N - 1):
            mt[i] = (
                mt[i]
                ^ ((mt[i - 1] ^ LShR(mt[i - 1], 30)) * BitVecVal(1566083941, 32))
            ) - BitVecVal(i, 32)
            # mt[i] ^= (mt[i-1] ^ (mt[i-1] >> 30)) * 1566083941
            # mt[i] -= i

            i += 1
            if i >= N:
                mt[0] = mt[N - 1]
                i = 1

        # 第三阶段：强制设置 mt[0] = 0x80000000
        mt[0] = BitVecVal(0x80000000, 32)

        # 约束：生成的 MT 状态必须等于我们恢复的目标状态
        s = Solver()
        for idx in range(N):
            s.add(mt[idx] == BitVecVal(target_state[idx], 32))

        if s.check() != sat:
            continue  # 该 key_words 无解，尝试下一个

        model = s.model()
        words = [model[k].as_long() & WORD_MASK for k in key]

        # 用正向方法验证（确保不是 Z3 的误报）
        if python_state_from_seed_words(words) == target_state:
            print(f"[+] found valid seed with key_words = {key_words}")
            return words

    raise RuntimeError("z3 failed to recover seed words for all key lengths 1..8")


def words_to_key(words_le: List[int], key_len: int = 32) -> bytes:
    """
    将 little-endian 的 32 位种子字转换为 big-endian 的字节串（即 AES 密钥）
    """
    seed_int = 0
    for i, w in enumerate(words_le):
        seed_int |= (w & WORD_MASK) << (32 * i)
    return seed_int.to_bytes(key_len, "big")


# ============================================================
# 解密 flag
# ============================================================
def decrypt_flag(master_key: bytes, nonce: bytes, ct: bytes, tag: bytes) -> bytes:
    """
    用恢复的 master_key 解密 flag
    flag 是用标准 AES-GCM 加密的（标签正确），所以直接解密即可
    """
    return AESGCM(master_key).decrypt(nonce, ct + tag, None)


# ============================================================
# 主攻击流程
# ============================================================
def main():
    # --- 第 1 步：连接服务器，获取 flag 的加密信息 ---
    io = remote("manytags.opus4-7.b01le.rs", 8443, ssl=True)
    banner = recv_menu(io)
    flag_nonce, flag_ct, flag_tag, budget = parse_initial(banner)

    print(f"[+] budget = {budget}")
    print(f"[+] flag_nonce = {flag_nonce.hex()}")
    print(f"[+] flag_ct = {flag_ct.hex()}")
    print(f"[+] flag_tag = {flag_tag.hex()}")

    assert budget == QUERY_BUDGET

    # --- 第 2 步：收集所有 704 个查询 ---
    # 每个查询返回 (密文, 污染标签)
    # 污染标签的低 64 位 = GHASH(H,C) 的低 64 位 XOR MT19937 的 64 位输出
    queries = collect_all_queries_fast(io, budget)
    print(f"[+] collected {len(queries)} queries")

    # --- 第 3 步：建立并求解 GF(2) 线性方程组 ---
    # 20096 个未知数，45056 个方程 → 有唯一解
    H, mt_state = recover_h_and_mt_state(queries)
    print(f"[+] H = {H:032x}")

    # 验证恢复结果
    check_mt_state_recovery(mt_state, queries, H, 8)

    # --- 第 4 步：从 MT 状态反推种子（即 AES 密钥）---
    seed_words = recover_seed_words_with_z3(mt_state, 8)
    print("[+] recovered seed words:")
    for i, w in enumerate(seed_words):
        print(f"    w[{i}] = {w:08x}")

    master_key = words_to_key(seed_words, 32)
    print(f"[+] master_key = {master_key.hex()}")

    # --- 第 5 步：用恢复的密钥解密 flag ---
    pt = decrypt_flag(master_key, flag_nonce, flag_ct, flag_tag)
    print(f"[+] flag = {pt!r}")


if __name__ == "__main__":
    main()

'''
#!/usr/bin/env python3
import random
import secrets

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

# AES相关常量
BLOCK_SIZE = 16  # AES块大小：16字节
BLOCK_BITS = 8 * BLOCK_SIZE  # 128位
MASK64 = (1 << 64) - 1  # 64位掩码（低64位全1）
MASK128 = (1 << BLOCK_BITS) - 1  # 128位掩码（全1）
GCM_REDUCTION = 0xE1000000000000000000000000000000  # GCM模式下GF(2^128)的约化多项式
# 在 GCM 规范中，为了让软件处理更高效，多项式的系数是反向填充到一个 128 位块中的。
# 也就是说，最低次幂 x^0 在最左边（最高位），最高次幂 $x^{127}$ 在最右边（最低位）

STATE_SIZE = 624  # Mersenne Twister状态大小（624个32位整数）
QUERY_BUDGET = 704  # 可以查询的次数上限
WORD_MASK = 0xFFFFFFFF  # 32位掩码

# 生成32字节随机主密钥
master_key = secrets.token_bytes(32)
used = 0  # 已使用的查询次数计数器


def new_fault_rng(key):
    """使用密钥初始化一个random.Random实例作为"故障RNG"
    这个RNG会产生可控的"故障"值注入到GCM标签中"""
    return random.Random(int.from_bytes(key, "big"))


# 创建基于主密钥的故障RNG
mask_rng = new_fault_rng(master_key)


def aes_block_encrypt(key, block):
    """AES-ECB模式加密单个块
    这里用于GCM的内部操作（如生成hash子密钥）"""
    encryptor = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
    return encryptor.update(block) + encryptor.finalize()


def aes_gcm_encrypt(key, nonce, message):
    """AES-GCM加密，返回(密文, 认证标签)
    注意：这是标准的GCM加密，标签是正确计算的"""
    encrypted = AESGCM(key).encrypt(nonce, message, None)
    return encrypted[:-BLOCK_SIZE], encrypted[-BLOCK_SIZE:]  # 分离密文和16字节标签


def compute_h(key):
    """计算GCM的hash子密钥H = AES_K(0^128)
    H用于GHASH中的GF(2^128)乘法"""
    return aes_block_encrypt(key, b"\x00" * BLOCK_SIZE)


def gf_mul(x, y):
    """GF(2^128)域上的乘法
    x, y是128位整数，使用GCM的约化多项式"""
    z = 0
    v = x
    for i in range(BLOCK_BITS):  # 逐位处理128次
        if (y >> (127 - i)) & 1:  # 如果y的当前位是1
            z ^= v  # 累加v到结果
        if v & 1:  # v的最低位是1
            v = (v >> 1) ^ GCM_REDUCTION  # 右移并异或约化多项式
        else:
            v >>= 1  # 直接右移
    return z & MASK128


def ghash(subkey, blocks):
    """GHASH函数：计算认证数据的hash
    subkey: H值
    blocks: 需要认证的数据块列表（每个是128位整数）"""
    tag = 0
    for block in blocks:
        tag = gf_mul(tag ^ block, subkey)  # GHASH的迭代计算
    return tag


def compute_length_block(message_len):
    """构造GCM的长度块：len(A) || len(C)
    这里A(附加认证数据)长度为0，所以前8字节为0"""
    return (0).to_bytes(8, "big") + (message_len * 8).to_bytes(8, "big")


def compute_one_block_ghash(h_int, ciphertext):
    """计算单个密文块的GHASH值（包含长度块）
    这个函数简化了GHASH，假设只有密文没有附加数据"""
    return ghash(
        h_int,
        [
            int.from_bytes(ciphertext, "big"),  # 密文块
            int.from_bytes(compute_length_block(len(ciphertext)), "big"),  # 长度块
        ],
    )


def compute_gcm_mask(key, nonce):
    """计算GCM的初始计数器块的加密结果
    用于生成认证标签的掩码：E_K(nonce || 0^31 || 1)"""
    return aes_block_encrypt(key, nonce + b"\x00\x00\x00\x01")


def construct_tag(real_tag, ghash_value, fault_words):
    """
    【核心漏洞函数】构造带有故障的认证标签
    
    GCM正常标签计算：tag = GHASH(H, A, C) ^ E_K(nonce || 1)
    
    这个函数故意在标签的低64位注入故障：
    1. 取出真实标签
    2. 用fault_words组合成64位故障值
    3. 只修改标签的低64位：new_low = GHASH ^ fault_value
    4. 保持高64位不变
    
    这样输出的标签就不是正确的GCM标签了！
    """
    real_tag_int = int.from_bytes(real_tag, "big")
    fault_value = (fault_words[0] << 32) | fault_words[1]  # 组合两个32位值成64位
    tag_low = (ghash_value ^ fault_value) & MASK64  # 低64位 = GHASH XOR 故障值
    tag_int = (real_tag_int & (~MASK64)) | tag_low  # 替换低64位
    return tag_int.to_bytes(BLOCK_SIZE, "big")


def encrypt_query_message(key, nonce, message, fault_words):
    """
    加密查询消息并故意产生错误的标签
    返回的tag包含注入的故障，不是真实的GCM标签
    """
    ciphertext, real_tag = aes_gcm_encrypt(key, nonce, message)
    h_int = int.from_bytes(compute_h(key), "big")
    ghash_value = compute_one_block_ghash(h_int, ciphertext)
    tag = construct_tag(real_tag, ghash_value, fault_words)  # 构造假标签
    return {
        "ciphertext": ciphertext,
        "real_tag": real_tag,  # 注意：返回了真实标签！（重要线索）
        "tag": tag,  # 这是给用户的假标签
        "ghash": ghash_value.to_bytes(BLOCK_SIZE, "big"),
    }


def next_fault_words(rng):
    """
    从RNG中生成下两个"故障字"
    每次查询会消耗RNG的64位熵（两个32位随机数）
    """
    return [rng.getrandbits(32), rng.getrandbits(32)]


def encrypt_query_with_rng(key, nonce, message, rng):
    """使用RNG生成故障并加密查询"""
    fault_words = next_fault_words(rng)
    result = encrypt_query_message(key, nonce, message, fault_words)
    result["fault_words"] = fault_words  # 注意：fault_words不返回给用户
    return result


def encrypt_flag_message(key, nonce, message):
    """
    加密flag消息
    关键：这里使用的是标准GCM加密，没有注入故障！
    flag的标签是正确计算的
    """
    return aes_gcm_encrypt(key, nonce, message)


def get_tag():
    """
    提供给用户的查询接口
    每次调用会：
    1. 生成随机nonce和消息
    2. 使用故障RNG加密（标签有故障）
    3. 返回nonce、密文和故障标签
    4. 递增计数器
    
    限制：最多查询QUERY_BUDGET(704)次
    """
    global used

    if used >= QUERY_BUDGET:
        print("No more tags for you")
        return

    nonce = secrets.token_bytes(12)
    message = secrets.token_bytes(BLOCK_SIZE)
    result = encrypt_query_with_rng(master_key, nonce, message, mask_rng)
    used += 1
    print(f"nonce = {nonce.hex()}")
    print(f"ciphertext = {result['ciphertext'].hex()}")
    print(f"tag = {result['tag'].hex()}")  # 只输出故障标签
    print(f"queries_left = {QUERY_BUDGET - used}")


def main():
    with open("./flag.txt") as f:
        flag = f.read().strip().encode()

    # 生成flag的加密结果（使用标准GCM，标签正确）
    flag_nonce = secrets.token_bytes(12)
    flag_cipher, flag_tag = encrypt_flag_message(master_key, flag_nonce, flag)

    print(f"""
*********************************************************

too many tags

*********************************************************

flag_nonce = {flag_nonce.hex()}
flag_ciphertext = {flag_cipher.hex()}
flag_tag = {flag_tag.hex()}  # flag的正确标签

query budget = {QUERY_BUDGET}

************************* Menu **************************

1. Get a random ciphertext and tag  # 获取有故障的标签
2. Exit

*********************************************************
""")

    while True:
        try:
            option = input("> ")
        except EOFError:
            return

        if option == "1":
            get_tag()
        elif option == "2":
            print("Bye")
            return
        else:
            print("Invalid option")


if __name__ == "__main__":
    main()
'''