import angr
import claripy
import logging

# logging.getLogger('angr.sim_manager').setLevel('INFO')

base_addr = 0x100000
# base_addr = 0

load_options = {}
load_options['force_load_libs'] = ['./libs/verify' + str(i) + '.so' for i in range(100)]
# load_options['except_missing_libs'] = True

class Avoid(angr.SimProcedure):
	def run(self, *skip):
		print("skip function call")
		return 0

class BugFree(angr.SimProcedure):
	def run(self, frm, name):
		# it is a pointer
		print(name)
		name = self.state.mem[name.to_claripy()].string.concrete
		# bytes
		print(name)
		name = name.decode('utf-8')
		lo = list(p.loader.find_all_symbols(name))
		print(lo)
		return lo[1].rebased_addr

p = angr.Project('./100libs.elf',
	main_opts={'base_addr': base_addr},
	load_options=load_options,
	auto_load_libs=True,
	)

p.hook_symbol('dlopen', Avoid())
p.hook_symbol('dlsym', BugFree())

bytes_list = [claripy.BVS('byte_%d' % i, 8) for i in range(256)]
data = claripy.Concat(*bytes_list)

"""
filename = 'answer'

libs = []

for i in range(100):
	libs.append("./libs/verify" + str(i) + ".so")
"""

state = p.factory.entry_state(
	stdin = data,
#	add_options={angr.options.ZERO_FILL_UNCONSTRAINED_REGISTERS, angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY},
#	add_options={angr.options.LAZY_SOLVES, angr.options.ZERO_FILL_UNCONSTRAINED_REGISTERS, angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY},
####	load_options={'force_load_libs': libs, 'auto_load_libs': False},
	)
"""
for i in bytes_list[:-1]:
	state.solver.add(i >= 32)
	state.solver.add(i <= 127)
state.solver.add(bytes_list[-1] == 0)
"""

def printBr(st):
	return lambda s: print("@@@@@@@@@@@@@@@@@", st)

# state.inspect.b('instruction', instruction=base_addr+0x20E4, when=angr.BP_BEFORE, action=printBr("oops"))
# state.inspect.b('instruction', instruction=base_addr+0x20C3, when=angr.BP_BEFORE, action=printBr("postscan"))

sm = p.factory.simulation_manager(state)


print("start exploration")

def testDbg(s):
	for i in range(3):
		print(i, "->", s.posix.dumps(i))
	return 'no'.encode('utf-8') in s.posix.dumps(1)

sm.explore(find=lambda s: 'YES'.encode('utf-8') in s.posix.dumps(1))
# sm.explore(find=lambda s: 'no'.encode('utf-8') in s.posix.dumps(1))
# sm.explore(find=testDbg)

print("start concretize")
print(sm.found)
for s in sm.found:
	print("!!!")
	test = s.solver.eval_upto(data, 3)
	for i in test:
		print(repr(i))
		print(i.to_bytes(len(bytes_list), byteorder='big'))