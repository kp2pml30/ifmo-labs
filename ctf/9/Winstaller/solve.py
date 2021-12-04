# python3 pyinstxtractor.py pyinstallerwin.exe

# uncompyle6 version 3.5.0
# Python bytecode 3.8 (3413)
# Decompiled from: Python 2.7.5 (default, Nov 16 2020, 22:23:17) 
# [GCC 4.8.5 20150623 (Red Hat 4.8.5-44)]
# Embedded file name: E:\AetherEternity\PycharmProjects\spbctfpytask\pyinstallerwin.py
import base64
flag = '==Qf==QT==AN==gU==QO==AM==gU==AU==wX==AT==AN==Qb==gU==AM==gT==wX==AN==wX==wM==wS==QM==AT==wX==wN==wU==QV==gS==wX==wd==AM==wV==we==gR==AV==wQ==gY==AU==wU'


f = flag[::-1].split('==')
print(f)
mp = list(map(lambda x: base64.b64decode(x + '==').decode('utf-8'), f))
print(mp)
print("</")
print(''.join(mp))
print(">/")

res = ''
text = input('Please enter the flag:\n')
for i in text:
    res += base64.b64encode(i.encode())


if flag == res[::-1]:
    print('Flag is corect')
else:
    print('Flag is incorect')