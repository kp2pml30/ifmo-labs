int foo(int b) {
	return b * b;
}

int select(int c, int t, int e) {
	if (c) {
		return t;
	} else {
		return e;
	}
}

void print(int f) {
	printf("%d\n", f);
}

void printNonZero(int f) {
	if (f) {
		print(f);
	}
}

void shadowing() {
	int x = 10;
	if (1) {
		int x = 12;
		print(x);
	}
	print(x);
}

int main(int argc, char** argv) {
	int a = 11;
	int b = 12;
	printf("%d\n", a + foo(b));
	print(13 + 14 + 15 + (16 + 17));
	int d = 13+14*15 / (16 + 17);
	int e = (13 + 14) * 15;
	if (0) {
		print(d + e);
	} else {
		int nestedunused111 = 11;
		print(d - e);
	}
	print(d * e);
	shadowing();
	return 0;
}
