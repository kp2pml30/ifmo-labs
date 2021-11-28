#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Don't forget to install pwntools: pip3 install pwntools.
# You need to write only process_equations function, all work with sockets is already done.
# Pass DEBUG as argument to see all client-server interaction: python3 crossword_template.py DEBUG

import pwn
import base64
import subprocess
import time

def solve():
	r = pwn.remote('109.233.56.90', 63175)

	r.recvline()
    
	while True:
		print()

		line = r.recvline().decode().strip()

		if len(line) < 200:
			print(line)
		else:
			print("file")
			with open("./f.elf", "wb") as f:
				f.write(base64.b64decode(line))
			start_time = time.time()
			result = subprocess.Popen('python3 ./a.py', shell=True, stdout=subprocess.PIPE)
			for line in result.stdout:
				print("elspased", time.time() - start_time)
				print(line)
				result = line.decode('utf-8').strip()
				break
			print("Result:", result)
			r.sendline(result)


if __name__ == "__main__":
    solve()