c="f000ae7e94f48ef99da6390f99a08701cf16d63596bebac938ec36004d54b73d1712c2f38926c3bcc5e5f42c4d55b57ef1070a7b443677b3cc4372d9a41a4775"
c=int(c,16)
c_bytes = c.to_bytes((c.bit_length() + 7) // 8, 'big')
print(c_bytes)
print(len(c_bytes))