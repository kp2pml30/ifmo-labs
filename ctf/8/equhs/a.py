import angr
import claripy

import logging

logging.getLogger('angr.sim_manager').setLevel('INFO')

# base_addr = 0x100000
base_addr = 0


p = angr.Project(
	'./equhs',
	# './equhs',
	# main_opts={'base_addr': base_addr}
)

bytes_list = [claripy.BVS('byte_%d' % i, 8) for i in range(30)]
data = claripy.Concat(*bytes_list)

filename = 'answer'
simfile = angr.SimFile(filename, content=data, has_end=True)

state = p.factory.full_init_state(
	stdin=simfile,
	fs={filename: simfile},
	add_options={angr.options.ZERO_FILL_UNCONSTRAINED_REGISTERS, angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY}
	)

for byte in bytes_list:
#	state.solver.add(byte >= 32)
	state.solver.add(byte <= 127)

sm = p.factory.simulation_manager(state)

def testres(s):
	print(s.posix.dumps(1))
	return True

sm.explore(find=testres)

print(sm.found)

for s in sm.found:
	test = s.fs.get(filename).concretize()
	print(test)
	for i in range(len(test)):
		if test[i] == 0:
			test = test[:i]
			break
	print(test.decode('utf-8'))