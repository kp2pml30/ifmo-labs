import angr
import claripy
import logging

# logging.getLogger('angr.sim_manager').setLevel('INFO')

# base_addr = 0x100000
base_addr = 0

p = angr.Project('./100libs.elf', main_opts={'base_addr': base_addr})

# bytes_list = [claripy.BVS('byte_%d' % i, 8) for i in range(40)]
# data = claripy.Concat(*bytes_list)

filename = 'answer'
#simfile = angr.SimFile(filename, content=data, has_end=False) # content=data

fle = angr.SimFileStream(name='stdin', has_end=False)

state = p.factory.full_init_state(
	stdin=fle,
#	args=[p.filename, filename],
	fs={filename: fle}
#	add_options={angr.options.LAZY_SOLVES}
	)

# for byte in bytes_list:
#	state.solver.add(byte >= 32)
#	state.solver.add(byte <= 127)

# state.solver.add(bytes_list[-1] == 0)
# state.solver.add(bytes_list[3] == 0)
# state.solver.add(bytes_list[0] == ord('a'))

def printBr(st):
	return lambda s: print("@@@@@@@@@@@@@@@@@", st)

# state.inspect.b('instruction', instruction=base_addr+0x125E, when=angr.BP_BEFORE, action=printBr("preread"))

sm = p.factory.simulation_manager(state)

print("start exploration")
sm.explore(find=base_addr+0x3006)
# sm.explore(find=base_addr+0x12B2)

print("start concretize")
print(sm.found)
for s in sm.found:
	print("!!!")
	test = s.fs.get(filename).concretize()
	print(repr(test))