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

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(5
abc
abcdr
abcde
xa
xb
xabcdef
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

std::vector<Suf> buildSuf(std::string const& findIn) noexcept
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

std::string_view smartSub(std::string const& s, int f, int l)
{
	if (f + l > s.size())
		return std::string_view(s.c_str() + f, s.size() - f);
	return std::string_view(s.c_str() + f, l);
}

bool findInSuf(std::vector<Suf> const& suf, std::string const& base, std::string const& wht)
{
	int l = -1;
	int r = suf.size();
	while (l < r - 1)
	{
		auto m = (l + r) / 2;
		auto res = smartSub(base, suf[m].ind, wht.size()).compare(wht);
		if (res < 0)
			l = m;
		else if (res > 0)
			r = m;
		else
			return true;
				
	}
	if (r >= suf.size())
		return false;
	return smartSub(base, suf[r].ind, wht.size()) == wht;
}

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	int m;
	cin >> m;
	std::vector<std::string> vec(m);

	{
		std::string e;
		std::getline(cin, e);
	}

	for (int i = 0; i < m; i++)
		std::getline(cin, vec[i]);
	std::string str;
	std::getline(cin, str);
	auto s = buildSuf(str);
	for (auto const& a : vec)
		if (findInSuf(s, str, a))
			cout << "YES\n";
		else
			cout << "NO\n";
	return 0;
}