# uncompyle6 version 3.5.0
# Python bytecode 3.8 (3413)
# Decompiled from: Python 2.7.5 (default, Nov 16 2020, 22:23:17) 
# [GCC 4.8.5 20150623 (Red Hat 4.8.5-44)]
# Embedded file name: pyinstallerelf.py
import os
from claripy import *

flag = '(d=\x01eq\x0c8V1\x10\x03!\x0f 6c\x19fgS\x0f8*?<=%1rfa\x00\x0f\x11;'
flagbytes = flag.encode()

bytesl = [BVS('x%i' % i, 8) for i in range(len(flag) + 6)]
solver = Solver()
for i, c in zip(range(0, 10**9), 'SPbCTF{'):
    solver.add(bytesl[i] == ord(c))

for c in bytesl:
    solver.add(c <= 127)
    solver.add(c >= 32)
for c in range(len(flagbytes)):
    solver.add(flagbytes[c] == bytesl[c % 6] ^ bytesl[c + 6])

mystr = ''

for i in bytesl:
	mystr += chr(solver.eval(i, 1)[0])
print(mystr)



res = ''
# text = input('Insert flag to continue playing:\n').encode()
text = mystr.encode()
flagd = text[:6]

# for i in range(6):
#    solver.add(flagbytes[i] == )

c = 0
for i in text[6:]:
    res += chr(i ^ flagd[(c % 6)])
    c += 1

print('@flag')
print(flagbytes)
print('@res')
print(res.encode())

if res == flag:
    print('Enjoy!')
else:
    print('That is definitely not a flag.')