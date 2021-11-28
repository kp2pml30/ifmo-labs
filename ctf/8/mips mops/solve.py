import angr
import claripy
import logging

logging.getLogger('angr.sim_manager').setLevel('DEBUG')

base_addr = 0x100000
# base_addr = 0

p = angr.Project('./mips_mops.elf', main_opts={'base_addr': base_addr})

bytes_list = [claripy.BVS('byte_%d' % i, 8) for i in range(33)]
data = claripy.Concat(*bytes_list)

state = p.factory.full_init_state(
	args=[p.filename, data],
#	add_options={angr.options.LAZY_SOLVES}
#	add_options={angr.options.LAZY_SOLVES, angr.options.ZERO_FILL_UNCONSTRAINED_REGISTERS, angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY}
	add_options={angr.options.ZERO_FILL_UNCONSTRAINED_REGISTERS, angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY}
	)

for byte in bytes_list[0:-1]:
	state.solver.add(byte >= 32)
	state.solver.add(byte <= 127)

state.solver.add(bytes_list[-1] == 0)

def printBr(st):
	return lambda s: print("@@@@@@@@@@@@@@@@@", st)

# state.inspect.b('instruction', instruction=base_addr+0x125E, when=angr.BP_BEFORE, action=printBr("preread"))

sm = p.factory.simulation_manager(state)

print("start exploration")
# sm.explore(find=base_addr+0x132C)
sm.explore(find=lambda s: "Serial is correct".encode('utf-8') in s.posix.dumps(1))
# sm.explore(find=base_addr+0x12FC, avoid=(base_addr+0x132C, base_addr+0x954))

print("start concretize")
print(sm.found)
for s in sm.found:
	print("!!!")
	test = s.solver.eval(data)
	print(repr(test))
	print(test.to_bytes(len(bytes_list), byteorder='little'))
	print(test.to_bytes(len(bytes_list), byteorder='big'))