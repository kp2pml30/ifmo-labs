f = open('tmp', 'r')

s = [set() for i in range(6)]

def breakline(l):
	lst = []
	while len(l) > 0:
		lst.append(l[:6])
		l = l[7:]
	return lst

for l in f.readlines():
	br = breakline(l)
#	print(br)
	for i in range(6):
 		s[i].add(br[i])

for si in s:
	print(">>>")
	for e in si:
		print("", e)

# SPBCTF
# EXPLOR
# ECOOL1
# ANGRFE
# ATURE1
# ???