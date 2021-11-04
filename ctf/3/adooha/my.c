#include <stdio.h>
#include <stdlib.h>

static char** offsets = (char**)0x6020C0;

static long long (*check)(long long) = (long long (*)(long long))0x400765;

void kp2hack() {
	for (int i = 0; i < 100; i++) {
		char* s1 = offsets[i * 2];
		char *s2 = offsets[i * 2 + 1];
		long long stol = strtol(s2, 0, 16);
		long long ch = (*check)((long long)s1);
		if (ch == stol) {
			printf("%d,", i);
		}
	}
	printf("\n");
}
