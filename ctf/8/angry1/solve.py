import angr
import claripy

# base_addr = 0x100000  main_opts={'base_addr': base_addr}, 

bin = './t1_t2_t3'

p = angr.Project(bin, auto_load_libs=True)

stdin = claripy.BVS('stdin', 0x40*8)

state = p.factory.entry_state(stdin=stdin)

def assertBytesOk(v, b):
	cond = v
	for i in range(b):
		state.solver.add(cond % 256 >= ord('+'))
		state.solver.add(cond % 256 <= ord('9'))
		cond = cond >> 8

# assertBytesOk(stdin, 20)

sm = p.factory.simulation_manager(state)

sm.explore(find=0x040126E)
print(sm.found)
for s in sm.found:
	evalNum = lambda x: trailZeros(s.solver.eval(x, cast_to=bytes).decode('utf-8'))
	print("------")
	print(s.solver.eval(stdin, cast_to=bytes).decode('utf-8'))