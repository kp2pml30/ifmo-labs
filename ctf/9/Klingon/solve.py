locs = {
	1: (68, 78),
	2: (133, 78),
	3: (202, 78),
	4: (268, 78),
	5: (268, 139),
	6: (202, 139),
	7: (133, 139),
	8: (68, 139),
	9: (268, 200),
	10: (202, 200),
	11: (133, 200),
	12: (68, 200),
	13: (268, 260),
	14: (202, 260),
	15: (133, 260),
	16: (68, 260),
}

from hashlib import md5

xs = list(set(map(lambda x: x[0], locs.values())))
ys = list(set(map(lambda x: x[1], locs.values())))
xs.sort()
ys.sort()
xm = {}
ym = {}
for i in range(4):
	xm[xs[i]] = i
	ym[ys[i]] = i

d = {}

for i in range(256):
	s = hex(i)[2:].upper()
	m = md5(s.encode())
	d[m.hexdigest()] = i

hashes = [ "06fa567b72d78b7e3ea746973fbbd1d5", "142ba1ee3860caecc3f86d7a03b5b175", "54229abfcfa5649e7003b83dd4755294", "8d2b901035fbd2df68a3b02940ff5196", "727999d580f3708378e3d903ddfa246d", "ea8a1a99f6c94c275a58dcd78f418c1f", "c51ce410c124a10e0db5e4b97fc2af39", "a5bfc9e07964f8dddeb95fc584cd965d" ]

def pr(a):
	l = locs[a + 1]
	print(ym[l[1]], xm[l[0]])

def fetch(x):
	g = d[x]
	pr(g // 16)
	pr(g % 16)

for i in hashes:
	fetch(i)
