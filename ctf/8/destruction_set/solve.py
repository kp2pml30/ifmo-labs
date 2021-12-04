import angr
import claripy
import logging

# logging.getLogger('angr.sim_manager').setLevel('DEBUG')

base_addr = 0x100000
# base_addr = 0

p = angr.Project('./destruction_set.elf',
	main_opts={'base_addr': base_addr}
	)

# bytes_list = [claripy.BVS('byte_%d' % i, 8) for i in range(64)]
# data = claripy.Concat(*bytes_list)
data = claripy.BVS('data', 8*8)

state = p.factory.entry_state(
	args=[p.filename, '--skipintro'],
#	stdin='123\n',
#	add_options={angr.options.LAZY_SOLVES}
#	add_options={angr.options.LAZY_SOLVES, angr.options.ZERO_FILL_UNCONSTRAINED_REGISTERS, angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY}
	add_options={angr.options.ZERO_FILL_UNCONSTRAINED_REGISTERS, angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY}
	)

"""
for byte in bytes_list[0:-1]:
	state.solver.add(byte >= 32)
	state.solver.add(byte <= 127)

state.solver.add(bytes_list[-1] == 0)
"""

def printBr(msg):
	def res(s):
		rsi = s.solver.eval(s.regs.rsi)
		s.mem[rsi].uint64_t = data
		print("@@@@@@@@@@@@@@@@@", msg, rsi)
	return res

state.inspect.b('instruction', instruction=base_addr+0x12BF, when=angr.BP_BEFORE, action=printBr("reading"))

sm = p.factory.simulation_manager(state)

def testOut(s):
	out = s.posix.dumps(1)
	print(out)
#	return "have not disarmed".encode('utf-8') in out
	return "Yaaaay".encode('utf-8') in out

print("start exploration")
# sm.explore(find=base_addr + 0x20f)
# sm.explore(find=base_addr + 0x13E5)
# sm.explore(find=base_addr + 0x12c4)
# sm.explore(find=testOut)
sm.explore(find=base_addr + 0x13D7) # yay
# sm.explore(find=base_addr + 0x13FB) # boom

print("start concretize")
print(sm.found)
for s in sm.found:
	print("!!!")
	test = s.solver.eval(data)
	print(test)
	print(oct(test))