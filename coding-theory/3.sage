import sys
from sage import *

if len(sys.argv) != 3:
	print('Usage: n, d')
	exit(1)
q = 2
n = int(sys.argv[1])
d = int(sys.argv[2])
k = None

print(f'q = {q}\nn = {n}\nd = {d}\nk = {k}')

def ham(q, n, d):
	t = (d - 1) // 2
	sm = 0
	for i in range(t+1):
		sm += binomial(n, i) * (q - 1) ^ i
	return log(q^n / sm, 2)

def ham_test(q, n, d, k):
	return k <= ham(q, n, d)

def greism(q, n, d, k):
	sm = 0
	for i in range(k):
		sm += ceil(d / 2^i)
	return sm

def greism_test(q, n, d, k):
	return n < greism(q, n, d, k)

def gilbVarch(q, n, d, k):
	sm = 0
	for i in range(d - 2 + 1):
		sm += binomial(n - 1, i) * (q-1)^i
	return sm

def gilbVarch_test(q, n, d, k):
	r = n - k
	return q^r <= gilbVarch(q, n, d, k)

"""
def opt(t):

print(f'Hamming {ham(q, n, d).n()}')
print(f'Griesmer_k {greism_k(q, n, d).n()}')
print(f'Gilbert-Varshamov_k {gilbVarch_k(q, n, d).n()}')
"""

k = d
d = None

print(f'q = {q}\nn = {n}\nd = {d}\nk = {k}')

