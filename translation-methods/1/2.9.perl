while (<>) {
	s/\(.*?\)/()/g;
	print;
}
