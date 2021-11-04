#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <vector>
#include <string>

namespace {

}

extern "C" {


void kp2hack(const long long key, const long long addr) {
	// addr: .text:000000000000138F
	const auto text = addr - 0x138F;
	auto *check = (char* (*)(char const*, char const*, char*))addr;
	char out[256];
	check("blood", (char const*)key, out);
	printf("ok\n%s\n", out);
	// .text:00000000000012A3
}

}
