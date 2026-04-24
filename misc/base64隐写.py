import base64

def get_base64_diff_value(s1, s2):
    base64chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
    for i in range(len(s2)):
        if s1[i] != s2[i]:
            return abs(base64chars.index(s1[i]) - base64chars.index(s2[i]))
    return 0

def goflag(bin_str):
    res_str = ''
    for i in range(0, len(bin_str), 8):
        chunk = bin_str[i:i + 8]
        res_str += chr(int(chunk, 2))
    return res_str

def solve_stego():
    with open(r'"F:\download\CTF\贝斯饭米粒.txt"', 'r', encoding='utf-8') as f:
        bin_str = ''
        for line in f:
            steg_line = line.strip()
            try:
                # 标准化处理
                decoded = base64.b64decode(steg_line.encode('ascii'))
                norm_line = base64.b64encode(decoded).decode('ascii')
            except Exception as e:
                print(f"跳过无效行: {line.strip()} (错误: {e})")
                continue

            diff = get_base64_diff_value(steg_line, norm_line)
            pads_num = steg_line.count('=')

            if diff:
                bin_str += bin(diff)[2:].zfill(pads_num * 2)
            else:
                bin_str += '0' * pads_num * 2

        print("解码结果:", goflag(bin_str))


if __name__ == '__main__':
    solve_stego()