import angr
import claripy
import logging

import sys

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

logging.getLogger('angr.sim_manager').setLevel('DEBUG')

base_addr = 0x100000
# base_addr = 0

p = angr.Project('./hasher2.elf', main_opts={'base_addr': base_addr}) # solved with this
# p = angr.Project('./hasher1-orig.elf', main_opts={'base_addr': base_addr})

bytes_list = [claripy.BVS('byte_%d' % i, 8) for i in range(42)]
data = claripy.Concat(*bytes_list)

state = p.factory.full_init_state(
	args=[p.filename, data],
#	add_options={angr.options.LAZY_SOLVES}
#	add_options={angr.options.LAZY_SOLVES, angr.options.ZERO_FILL_UNCONSTRAINED_REGISTERS, angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY}
	add_options={angr.options.ZERO_FILL_UNCONSTRAINED_REGISTERS, angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY}
	)

for i in range(41):
	byte = bytes_list[i]
	if i % 7 == 6:
		state.solver.add(byte == ord('-'))
	else:
		state.solver.add(byte <= ord('Z'))
		state.solver.add(byte >= ord('0'))
		for j in range(ord(':'), ord('A')):
			state.solver.add(byte != j)

# 012345678            21
# SPBCTF-

"""
state.solver.add(bytes_list[0] == ord('S'))
state.solver.add(bytes_list[1] == ord('P'))
state.solver.add(bytes_list[2] == ord('B'))

state.solver.add(bytes_list[7] == ord('Y'))
state.solver.add(bytes_list[8] == ord('O'))
state.solver.add(bytes_list[9] == ord('U'))


state.solver.add(bytes_list[21] == ord('A'))
state.solver.add(bytes_list[22] == ord('N'))
state.solver.add(bytes_list[23] == ord('G'))
"""

state.solver.add(bytes_list[-1] == 0)

def printBr(st):
	return lambda s: print("@@@@@@@@@@@@@@@@@", st)

# state.inspect.b('instruction', instruction=base_addr+0x125E, when=angr.BP_BEFORE, action=printBr("preread"))

sm = p.factory.simulation_manager(state)

eprint("start exploration")
#sm.explore(find=base_addr+0xFFD)
sm.explore(find=base_addr+0xE18)

eprint("start concretize")
eprint(sm.found)
for s in sm.found:
	for test in s.solver.eval_upto(data, 1000):
#	print(test.to_bytes(len(bytes_list), byteorder='little'))
		print(test.to_bytes(len(bytes_list), byteorder='big')[:-1].decode('ascii'))