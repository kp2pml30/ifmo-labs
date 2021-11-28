#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Don't forget to install pwntools: pip3 install pwntools.
# You need to write only process_equations function, all work with sockets is already done.
# Pass DEBUG as argument to see all client-server interaction: python3 crossword_template.py DEBUG

import pwn

from z3 import *

def process_equations(eq):
	d = {}
	stack = []
	tosolve = []
	def bopop(o): return o(stack.pop(), stack.pop())
	def bop(o): stack.append(bopop(o))
	for l in map(lambda x: x.split(), eq):
		for e in l:
#			print("stack:", stack)
#			print("2solv:", tosolve)
			if e == "-": bop(lambda x, y: x - y)
			elif e[0] >= '0' and e[0] <= '9' or e[0] == '-':
				stack.append(int(e))
			elif e == "+": bop(lambda x, y: x + y)
			elif e == "*": bop(lambda x, y: x * y)
			elif e == "/": bop(lambda x, y: x / y)
			elif e == "=": tosolve.append(bopop(lambda x, y: x == y))
			else:
				v = d.get(e)
				if v is None:
					v = Int(e)
					d[e] = v
				stack.append(v)
	s = Solver()
	s.add(*tosolve)
	r = s.check()
	m = s.model()
	s = ""
	for i in range(len(d)):
		s += chr(int(str(m.eval(d["x" + str(1 + i)]))))
	return s


def solve():
    r = pwn.remote('109.233.56.90', 11542)

    r.recvline()
    
    while True:
        print()

        line = r.recvline().decode().strip()
        print(line)

        if not line.startswith("Crossword"):
            return

        count = int(line.split()[4])
        
        lines = []
        for _ in range(count):
            lines.append(r.recvline().decode().strip())
        
        print("Equations:", lines)
        result = process_equations(lines)
        print("Result:", result)

        r.sendline(result)


if __name__ == "__main__":
    solve()