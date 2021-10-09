import scipy
import scipy.interpolate
import numpy
import re

__version__ = "0.1.0"
__credits__ = 'ITMO'

# install_requires=['numpy<=1.16.9999', 'scipy==1.7.1']

def get_np_ver():
	return numpy.__version__

def check_versions():
	return scipy.__version__ == '1.7.1' and re.match(r"1\.16\.[0-9]+", get_np_ver())

def get_zero():
	return scipy.interpolate.lagrange(numpy.arange(0, 1, 0.3), numpy.zeros(4))(0.2)