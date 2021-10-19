int print(int b) {
	printf("%d\n", b);
}

int main(int argc, char** argv) {
	printf("argc=%d\n", argc);
	int var = 11;
	print(var);
	return 0;
}
