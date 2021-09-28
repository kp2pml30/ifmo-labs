while (<>) {
	print if /^(|\S.*\S|\S)\r?\n?$/;
}
