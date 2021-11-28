import angr
import claripy
import logging

# logging.getLogger('angr.sim_manager').setLevel('INFO')

base_addr = 0x100000

p = angr.Project('./filegr.elf', main_opts={'base_addr': base_addr})

bytes_list = [claripy.BVS('byte_%d' % i, 8) for i in range(40)]
data = claripy.Concat(*bytes_list)

filename = 'answer'
simfile = angr.SimFile(filename, content=data, has_end=False) # content=data

state = p.factory.full_init_state(
	args=[p.filename, filename],
	fs={filename: simfile},
#	add_options={angr.options.LAZY_SOLVES}
	)

for byte in bytes_list:
#	state.solver.add(byte >= 32)
	state.solver.add(byte <= 127)

# state.solver.add(bytes_list[-1] == 0)
# state.solver.add(bytes_list[3] == 0)
# state.solver.add(bytes_list[0] == ord('a'))

def printBr(st):
	return lambda s: print("@@@@@@@@@@@@@@@@@", st)

state.inspect.b('instruction', instruction=base_addr+0x125E, when=angr.BP_BEFORE, action=printBr("preread"))
state.inspect.b('instruction', instruction=base_addr+0x126D, when=angr.BP_BEFORE, action=printBr("postread"))
state.inspect.b('instruction', instruction=base_addr+0x12B2, when=angr.BP_BEFORE, action=printBr("wrong size"))
state.inspect.b('instruction', instruction=base_addr+0x12CE, when=angr.BP_BEFORE, action=printBr("lenok"))

dummy_addr = 0x300000

state.inspect.b('instruction', instruction=base_addr+0x1278, when=angr.BP_BEFORE, action=printBr("checkenter"))

state.inspect.b('instruction', instruction=base_addr+0x12B2, when=angr.BP_BEFORE, action=printBr("wrong len"))
state.inspect.b('instruction', instruction=base_addr+0x12AA, when=angr.BP_BEFORE, action=printBr("afterlen"))

sm = p.factory.simulation_manager(state)

print("start exploration")
sm.explore(find=base_addr+0x1BFA, avoid=base_addr+0x12B2)
# sm.explore(find=base_addr+0x12B2)

print("start concretize")
print(sm.found)
for s in sm.found:
	print("!!!")
	print(s.solver.eval(data))
	test = s.fs.get(filename).concretize()
	print(repr(test))