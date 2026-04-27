import base64
import hashlib

def generate_code(username):
    rev = username[::-1]  # 字符串反转
    xor = "".join([chr(ord(c) ^ 7) for c in rev])
    code = base64.b64encode(xor.encode()).decode()
    md5 = hashlib.md5()
    md5.update(code.encode())
    return md5.hexdigest()

username = "XSWCTF"
expected_code = generate_code(username)
print(f"用户名: {username}")
print(f"注册码: {expected_code}")