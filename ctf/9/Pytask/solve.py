# uncompyle6 version 3.5.0
# Python bytecode 3.8 (3413)
# Decompiled from: Python 2.7.5 (default, Nov 16 2020, 22:23:17) 
# [GCC 4.8.5 20150623 (Red Hat 4.8.5-44)]
# Embedded file name: .\main.py
# Size of source mod 2**32: 509 bytes
flag = '35x005x026x034x045x064x0b7x023x056x013x053x053x063x073x073x046x053x083x023x043x056x083x053x056x066x043x013x003x093x043x016x056x036x073x016x083x033x046x036x0d7x0'

def check(text):
    global flag
    res = ''
    for i in text:
        add = hex(int.from_bytes(i.encode(), 'big'))[::-1]
        print(add, end='--')
        res += add
    print()
    return flag == res

solve = map(lambda x: chr(int(x[::-1], 16)), flag.split('x0')[:-1])
print(''.join(solve))

if __name__ == '__main__':
    flagin = input('Enter your flag: \n')
    if check(flagin):
        print('[+] You win!')
    else:
        print('[-] You lose!')