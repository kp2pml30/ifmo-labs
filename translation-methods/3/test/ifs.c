void print(int c) {
	printf("%d\n", c);
}

int select(int c, int t, int e) {
	if (c) {
		return t;
	} else {
		return e;
	}
}

void printNonZero(int c) {
	if (c) {
		print(c);
	}
}

int main() {
	printNonZero(0);
	printNonZero(30);
	printNonZero(20);
	printNonZero(0 - 0);
	printNonZero(0 - 1);
	print(select(10 - 10, 0 - 30, 30));
	print(select(10 + 10, 0 - 30, 30));
	return 0;
}
