from setuptools import setup

setup(
	name='garbage-dependencies',
	version='0.1.2',
	description='garbage project, sorry for pollution I am obligated to do so',
	url='https://github.com/kp2pml30',
	author='kp2pml30',
	author_email='kp2pml30@gmail.com',
	license='GPL 3',
	packages=['garbagedependencies'],
	install_requires=['numpy', 'scipy']
#	install_requires=['numpy<=1.17']
)