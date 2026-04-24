import string
import base64
with open(r'F:\download\CTF\base家族\base家族\base.txt') as f:
    text = f.read()
while(1):
    try:
        text = base64.b64decode(text).decode()
    except Exception as e:
        try:
            text = base64.b32decode(text).decode()
        except Exception as e:
            try:
                text = base64.b16decode(text).decode()
            except Exception as e:
                break
print(text)
