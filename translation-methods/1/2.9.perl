while (<>) {
	s/\(.*?\)/()/g;
	print;
}