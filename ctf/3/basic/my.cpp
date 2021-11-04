#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <vector>
#include <string>

namespace {

int correctInts[] = {8,24,24,19,8,17,26,31,6,4,26,21,30,16,18,1,10,13,2,21,30,19,26,6,11,29,0,20,28,22,8,10};

struct Saved {
	int outlen;
	int firstchar;
	int ind;
	int i;
};

int my_recode(std::string const& s)
{
	int outlen; // [rsp+20h] [rbp-18h]
	int firstchar; // [rsp+24h] [rbp-14h]
	int ind; // [rsp+28h] [rbp-10h]
	int i; // [rsp+2Ch] [rbp-Ch]

	if (s.empty()) {
		return 0;
	}

	outlen = 0;
	firstchar = s.front();
	ind = 1;
	for ( i = 8; i > 0 || ind < s.size(); i -= 5 )
	{
		if ( i <= 4 )
		{
			if ( ind >= s.size() )
			{
				firstchar <<= 5 - i;
				i = 5; // this one will terminate
			}
			else
			{
				firstchar = (firstchar << 8) | s[ind];
				ind++;
				i += 8;
			}
		}
		int ttt = (firstchar >> (i - 5)) & 0x1F;
		if (ttt != correctInts[outlen]) {
			return outlen;
		}
		outlen++;
	}
	return outlen;
}

Saved my_recode2(std::string const& s, Saved& initial)
{
	auto [outlen, firstchar, ind, i] = initial;
	// 0 'F' 1 8
	
	auto saved = Saved {-1, -1, -1, -1};

	for ( ; i > 0 || ind < s.size(); i -= 5 )
	{
		if (i <= 4 && ind >= s.size()) {
			return saved;
		}
		saved = Saved { outlen, firstchar, ind, i };
		if ( i <= 4 )
		{
			if ( ind >= s.size() )
			{
				firstchar <<= 5 - i;
				i = 5; // this one will terminate
			}
			else
			{
				firstchar = (firstchar << 8) | s[ind];
				ind++;
				i += 8;
			}
		}
		int ttt = (firstchar >> (i - 5)) & 0x1F;
		if (ttt != correctInts[outlen]) {
			return Saved {-1, -1, -1, -1};
		}
		outlen++;
	}
	return saved;
}

#if 0
void old_hack() {
	std::vector<std::string> queue = {"F14G_15_BASE_OF_ANX"};
	std::vector<std::string> next;
	const auto printQueue = [&queue]() {
		for (auto const& s : queue) {
			printf("%s\n", s.c_str());
		}
	};
	while (queue.front().size() <= 32) {
		for (auto& s : queue) {
			s += '_';
			for (int c = 48; c <= 95; c++) {
				s.back() = c;
				if (my_recode(s) >= s.size()) {
					next.emplace_back(s);
				}
			}
		}
		if (next.empty()) {
			printf("failed after\n");
			printQueue();
			return;
		}
		// printQueue();
		std::swap(queue, next);
		next.clear();
		printf(">>> %d has %d\n", queue.front().size(), queue.size());
		printf("\t%s\n", queue.front().c_str());
	}
	printQueue();
}
#endif

}

extern "C" {

static auto *check = (long long (*)(char const*, int, char*, int))0x4006BD;

static void brute_last(std::string& s) {
	// s += '_';
	printf("brute force\n");
	char buf[320] = {};
	for (int c1 = 0; c1 <= 126; c1++)
	{
	for (int c2 = 32; c2 <= 126; c2++)
	{
	// for (int c3 = 32; c3 <= 126; c3++)
	{
	// for (int c4 = 32; c4 <= 126; c4++)
	{
		s[s.size() - 1] = c1;
		s[s.size() - 2] = c2;
		// s[s.size() - 3] = c3;
		// s[s.size() - 4] = c4;
		(*check)(s.c_str(), s.size(), buf, 32);
		// printf("%s <- %s\n", buf, s.c_str());
		if (strcmp(buf, "IYYTIR27GE2V6QSBKNCV6T2GL5AU4WIK") == 0) {
			printf("answer %s\n", s.c_str());
		}
	}
	}
	}
	}
}

void kp2hack() {
	std::vector<std::pair<std::string, Saved>>
		queue = {{"F", Saved { 0, 'F', 1, 8 }}},
		next; // F14G_15_
	while (true) {
		for (auto& s : queue) {
			s.first += '_';
			for (int c = 32; c <= 126; c++) {
				s.first.back() = c;
				const auto nw = my_recode2(s.first, s.second);
				if (nw.i != -1) {
					next.emplace_back(s.first, nw);
				}
			}
		}
		if (next.empty()) {
			auto const& str = queue.front().first;
			printf("failed\n");
			printf(">>> %d has %d\n", str.size(), queue.size());
			printf("\t%s\n", str.c_str());
			brute_last(queue.front().first);
			return;
		}
		// printQueue();
		std::swap(queue, next);
		next.clear();
		printf(">>> %d has %d\n", queue.front().first.size(), queue.size());
		printf("\t%s\n", queue.front().first.c_str());
	}
}

}
