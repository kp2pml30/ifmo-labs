import angr
import claripy
import logging

load_options = {}

p = angr.Project('./smsserver.exe',
	load_options=load_options,
	auto_load_libs=True,
	)

bytes_list = [claripy.BVS('byte_%d' % i, 8) for i in range(256)]
data = claripy.Concat(*bytes_list)

mstraddr = 0xfff00fffffffff00

state = p.factory.blank_state(
	addr=0x10002BCCE,
	add_options={angr.options.LAZY_SOLVES, angr.options.ZERO_FILL_UNCONSTRAINED_REGISTERS, angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY},
	)

state.solver.add(bytes_list[-1] == 0)

for i in range(len(bytes_list)):
	byte = bytes_list[i]
	state.mem[mstraddr + i].uint8_t = byte
for i in range(1, 20):
	state.mem[mstraddr - i].uint8_t = 1
state.regs.rbp = 0x800
state.regs.rsp = 0x600
state.mem[0x800 - 8].uint64_t = mstraddr

sm = p.factory.simulation_manager(state)


print("start exploration")
logging.getLogger('angr.sim_manager').setLevel('INFO')
sm.explore(find=0x10002BD12) # , avoid=0x10002BD15)

print("start concretize")
print(sm.found)
for s in sm.found:
	print("!!!")
	test = s.solver.eval_upto(data, 3)
	for i in test:
		print(repr(i))
		print(i.to_bytes(len(bytes_list), byteorder='big'))