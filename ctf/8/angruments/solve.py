import angr
import claripy

# base_addr = 0x100000  main_opts={'base_addr': base_addr}, 

bin = './angruments'

p = angr.Project(bin, auto_load_libs=True)

a1 = claripy.BVS('a2', 6*8)
a2 = claripy.BVS('a1', 4*8)
a3 = claripy.BVS('a2', 4*8)

state = p.factory.entry_state(args=[bin, a1, a2, a3])

def assertBytesDigits(v, b):
	cond = v
	for i in range(b):
		state.solver.add(cond % 256 >= ord('0'))
		state.solver.add(cond % 256 <= ord('9'))
		cond = cond >> 8
assertBytesDigits(a2, 4)
assertBytesDigits(a3, 4)

# state = p.factory.blank_state(addr=0x400695)

"""
def seta1(x):
	x.regs.ebx = a1
def seta2(x):
	x.regs.ecx = a2
state.inspect.b('instruction', instruction=0x400696, when=angr.BP_AFTER, action=seta1)
state.inspect.b('instruction', instruction=0x4006AB, when=angr.BP_AFTER, action=seta2)
"""

sm = p.factory.simulation_manager(state)

"""
for i in range(10):
	print(sm.step())
exit(0)
"""

sm.explore(find=0x4006CD, avoid=0x4006DE)
print(sm.found)
for s in sm.found:
	print("------")
	v1 = s.solver.eval(a1, cast_to=bytes).decode('utf-8')
	v2 = s.solver.eval(a2, cast_to=bytes).decode('utf-8')
	while v2[0] == '0':
		v2 = v2[1:]
	v3 = s.solver.eval(a3, cast_to=bytes).decode('utf-8')
	print("flag{{{}{}{}}}".format(v1, v2, v3))
#	print(i.eval(a1))
#	print(i.eval(a2))
