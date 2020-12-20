// no dont look

#include <array>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <map>
#include <functional>
#include <set>
#include <unordered_set>
#include <list>
#include <memory>
#include <string_view>
#include <deque>

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(2
a
a
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
#endif

using uint = std::uint32_t;
using size_type = std::uint32_t;

struct Suf
{
	int ind, rank0, rank1;
	bool operator<(Suf const& b) const noexcept
	{
		if (rank0 == b.rank0)
			return rank1 < b.rank1;
		else
			return rank0 < b.rank0;
	}
};

std::vector<Suf> BuildSuffixArray(std::string const& findIn) noexcept
{
	auto n = findIn.size();
	std::vector<Suf> suff(n);
	for (int i = 0; i < n; i++)
		suff[i] = {i, findIn[i] - 90, (i + 1 < n) ? (findIn[i + 1] - 90) : -1};

	std::sort(suff.begin(), suff.end());
	std::vector<int> ind(n, 0);
	for (int k = 4; k < 2 * n; k *= 2)
	{
		int rank = 0;
		int prevRank = suff[0].rank0;
		suff[0].rank0 = 0;
		ind[suff[0].ind] = 0;

		for (int i = 1; i < n; i++)
		{
			if (suff[i].rank0 == prevRank && suff[i].rank1 == suff[i - 1].rank1)
			{
				prevRank = suff[i].rank0;
				suff[i].rank0 = rank;
			}
			else
			{
				prevRank = suff[i].rank0;
				rank += 1;
				suff[i].rank0 = rank;
			}
			ind[suff[i].ind] = i;
		}
		for (int i = 0; i < n; i++)
		{
			int nextInd = suff[i].ind + k / 2;
			suff[i].rank1 = (nextInd < n) ? suff[ind[nextInd]].rank0 : -1;
		}
		std::sort(suff.begin(), suff.end());
	}
	return suff;
}

std::vector<int> BuildLCP(std::string const& str, std::vector<Suf> const& suf)
{
	auto n = str.size();
	std::vector<int>
		ret(n, 0),
		reverse(n);

	for (int i = 0; i < n; i++)
		reverse[suf[i].ind] = i;

	int k = 0;
	for (int i = 0; i < n; i++)
	{
		if (k > 0)
			k--;
		if (reverse[i] == n - 1)
		{
			k = 0;
			continue;
		}
		int j = suf[reverse[i] + 1].ind;
		while (i + k < n
			&& j + k < n
			&& str[i + k] == str[j + k])
			k++;
		ret[reverse[i]] = k;
	}
	ret.pop_back();
	return ret;
}

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	int k;
	cin >> k;

	// volatile std::vector<char> kp2hack(k * 1024 * 1024, -1);

	{
		std::string e;
		std::getline(cin, e);
	}

	if (k == 1)
	{
		std::string e;
		std::getline(cin, e);
		std::cout << e << std::endl;
		throw "up";
	}

	std::string assembly;
	assembly.reserve(200000);
	std::vector<int> starts;
	std::vector<int> lengths;
	starts.reserve(10);
	lengths.reserve(10);
	for (int i = 0; i < k; i++)
	{
		auto olds = assembly.size();
		std::string s2;
		std::getline(cin, s2);
		lengths.push_back(s2.size());
		assembly += s2;
		assembly += char(33 + i);
		starts.emplace_back(assembly.size());
	}
	auto suff = BuildSuffixArray(assembly);
	auto lcp = BuildLCP(assembly, suff);

#if 0
	if (k == 2)
	{
		int res = 0;
		std::string_view brr;
		for (int i = 0; i < lcp.size(); i++)
		{
			if (suff[i].ind < s1 && suff[i + 1].ind > s1
				|| suff[i + 1].ind < s1 && suff[i].ind > s1)
				if (brr.size() < lcp[i])
					brr = std::string_view(assem.c_str() + suff[i].ind, lcp[i]);
		}
		cout << brr << std::endl;
		return 0;
	}
#endif

	std::vector<int> colors(suff.size(), -1);
	for (int i = 0; i < suff.size(); i++)
		for (int k1 = 0; k1 < starts.size(); k1++)
			if (suff[i].ind < starts[k1])
			{
				colors[i] = k1;
				break;
			}

	std::array<int, 13> current = {};
	int used = 0;
	std::deque<int> mins;

	auto significant = [&](int ind) {
		return current[colors[ind]] == 1;
	};
	auto put = [&](int ind) {
		while (!mins.empty() && mins.back() > lcp[ind - 1])
			mins.pop_back();
		if (mins.empty() || mins.back() <= lcp[ind - 1])
			mins.emplace_back(lcp[ind - 1]);
		current[colors[ind]]++;
		if (significant(ind))
			used++;
	};
	auto take = [&](int ind) {
		if (mins.front() == lcp[ind])
			mins.pop_front();
		if (significant(ind))
			used--;
		current[colors[ind]]--;
	};

	// invariant: [l..r) is taken
	int l = 0;
	int r = 0;
	current[colors[0]] = 1;
	used = 1;
	r = 1;

	std::string_view answer;

	while (true)
	{
		while (r < suff.size() && used != k)
			put(r++);
		if (used != k)
			break;
		while (!significant(l))
			take(l++);

		if (mins.front() > answer.size())
			answer = std::string_view(assembly.c_str() + suff[l].ind, mins.front());

		// to next
		take(l++);
	}

	std::cout << answer << std::endl;

	return 0;
}