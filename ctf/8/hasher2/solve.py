import angr
import claripy
import logging

# logging.getLogger('angr.sim_manager').setLevel('INFO')

base_addr = 0x100000

p = angr.Project('./hasher2.elf', main_opts={'base_addr': base_addr})

bytes_list = [claripy.BVS('byte_%d' % i, 8) for i in range(6*6+5)]
data = claripy.Concat(*bytes_list)

# filename = 'answer'
# simfile = angr.SimFile(filename, content=data, has_end=False) # content=data

state = p.factory.full_init_state(
	args=[p.filename, data],
#	fs={filename: simfile},
#	add_options={angr.options.LAZY_SOLVES}
	)

for i in range(len(bytes_list)):
	byte = bytes_list[i]
	if i % 7 == 6:
		state.solver.add(byte == ord('-'))
	else:
		state.solver.add(byte >= 48)
		state.solver.add(byte <= 90)

def printBr(st):
	return lambda s: print("@@@@@@@@@@@@@@@@@", st)

# state.inspect.b('instruction', instruction=base_addr+0x12CE, when=angr.BP_BEFORE, action=printBr("lenok"))

sm = p.factory.simulation_manager(state)

print("start exploration")
sm.explore(find=base_addr+0x1004)

print("start concretize")
print(sm.found)
for s in sm.found:
	print("!!!")
	e = s.solver.eval(data)
	print(e)
	print(e.to_bytes(100, byteorder='big'))
	print(e.to_bytes(100, byteorder='little'))