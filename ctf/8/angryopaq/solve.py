import angr
import claripy

bin = './angryopaq.elf'

base_addr = 0x0

p = angr.Project(bin, auto_load_libs=True)

v1 = claripy.BVS('a', 4*8)

state = p.factory.entry_state(stdin="13\n")

def seta1(state):
	rbp = state.solver.eval(state.regs.rbp)
	print("breaked", hex(rbp))
	state.mem[rbp - 0x24].uint32_t = v1

state.inspect.b('instruction', instruction=base_addr+0x401196, when=angr.BP_BEFORE, action=seta1)

sm = p.factory.simulation_manager(state)

print('exploring')
sm.explore(find = base_addr + 0x4015B9)
print(sm.found)
for s in sm.found:
	evalNum = lambda x: print(s.solver.eval(x))
	print("------")
	evalNum(v1)
	evalNum(v2)
	evalNum(v3)
	evalNum(v4)
	evalNum = lambda x: print(hex(s.solver.eval(x)))
	print("========")
	evalNum(v1)
	evalNum(v2)
	evalNum(v3)
	evalNum(v4)