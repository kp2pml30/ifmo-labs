import angr
import claripy

bin = './cheat.elf'

base_addr = 0x100000

p = angr.Project(bin, main_opts={'base_addr': base_addr}, auto_load_libs=True)

v1 = claripy.BVS('a', 4*8)
v2 = claripy.BVS('b', 4*8)
v3 = claripy.BVS('c', 4*8)
v4 = claripy.BVS('d', 4*8)

state = p.factory.entry_state(stdin="1254-1354-1454-1554\n")

#state.solver.add(v1 <= 0xffff)
#state.solver.add(v2 <= 0xffff)
#state.solver.add(v3 <= 0xffff)
#state.solver.add(v4 <= 0xffff)

def seta1(state):
	rbp = state.solver.eval(state.regs.rbp)
	print("breaked", hex(rbp))
	state.mem[rbp + 0x20].uint32_t = v1
	state.mem[rbp + 0x1C].uint32_t = v2
	state.mem[rbp + 0x18].uint32_t = v3
	state.mem[rbp + 0x14].uint32_t = v4

state.inspect.b('instruction', instruction=base_addr+0x12FA, when=angr.BP_BEFORE, action=seta1)

sm = p.factory.simulation_manager(state)

print('exploring')
sm.explore(find = base_addr + 0x1349)
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