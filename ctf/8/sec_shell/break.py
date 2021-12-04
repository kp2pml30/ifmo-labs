from claripy import *

rax = BVS('rax', 8*8)
rbx = BVS('rbx', 8*8)

rbx0 = rbx

s = Solver()

for i in range(8):
	s.add(((rbx >> (i * 8)) & 0xff) <= 127)

s.add(rax == 0x3546364654ACBBC7)
# s.add((rbx & 0xff) == 2)

for i in range(8):
	rbx = RotateRight(rbx, 8)
	rax = RotateRight(rax, 8)
	rbx = If(rbx & 0x1 == 0,
		rbx,
		rbx ^ 0xff)
	rax = (rax & 0xffffffffffffff00) | ((rax & 0xff) ^ (rbx & 0xff))

s.add(rax == 0x11D2F874308A73ED)

l = s.eval(rbx0, 100)

print(list(map(hex, l)))
print(list(map(lambda x: x.to_bytes(8, byteorder='big'), l)))
print(list(map(lambda x: x.to_bytes(8, byteorder='little'), l)))