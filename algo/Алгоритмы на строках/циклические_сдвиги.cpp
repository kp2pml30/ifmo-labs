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
auto cin = std::stringstream(R"delim(abacabac
4
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
#endif

using uint = std::uint32_t;
using size_type = std::uint32_t;


template<typename Descr>
class Tree
{
private:
	using type = typename Descr::type;
	Descr descr;
	std::vector<type> elements;
	uint n;
	class Setter
	{
	private:
		Tree *parent;
		uint index;
	public:
		Setter(Tree *parent, uint index) : parent(parent), index(index) {}
		void operator=(const type &r)
		{
			return parent->set(index, r);
		}
	};
	void set(uint i, const type &w)
	{
		i += n - 1;
		elements[i] = w;
		while (i > 0)
		{
			i = (i - 1) / 2;
			elements[i] = descr.oper(elements[2 * i + 1], elements[2 * i + 2]);
		}
	}
	type calc(uint l, uint r, uint x, uint lx, uint rx)
	{
		if (l >= rx || lx >= r)
			return descr.neutral;
		if (lx >= l && rx <= r)
			return elements[x];
		uint m = (lx + rx) / 2;
		return descr.oper(calc(l, r, 2 * x + 1, lx, m), calc(l, r, 2 * x + 2, m, rx));
	}
public:
	Tree(const std::vector<type> &els)
	{
		n = els.size();
		n--;
		n |= n >> 1;
		n |= n >> 2;
		n |= n >> 4;
		n |= n >> 8;
		n |= n >> 16;
		n++;
		elements.resize(2 * n - 1, descr.neutral);
		for (uint i = 0; i < els.size(); i++)
			elements[n - 1 + i] = els[i];
		for (int i = n - 2; i >= 0; i--)
			elements[i] = descr.oper(elements[2 * i + 1], elements[2 * i + 2]);
	}
	Setter operator[](uint i) { return Setter(this, i); }

	type operator()(uint l, uint r)
	{
		l += n - 1;
		r += n - 2;
		type
			ansl = descr.neutral,
			ansr = descr.neutral;
		while (l < r)
		{
			if (l % 2 == 0)
				ansl = descr.oper(ansl, elements[l]);
			l /= 2;
			if (r % 2)
				ansr = descr.oper(elements[r], ansr);
			r = r / 2 - 1;
		}
		if (l == r)
			ansl = descr.oper(ansl, elements[l]);
		return descr.oper(ansl, ansr);
	}
};

template<typename type>
class minimax
{
public:
	type operator()(const type &l, const type &r) noexcept
	{
		return {std::min(l.first, r.first), std::max(l.second, r.second)};
	}
};

class intdescr
{
public:
	using type = std::pair<int, int>;
	minimax<type> oper;
	const type neutral = {16714588, -1};
};

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

std::string_view SmartSubstr(std::string const& s, int f, int l)
{
	if (f + l > s.size())
		return std::string_view(s.c_str() + f, s.size() - f);
	return std::string_view(s.c_str() + f, l);
}

int SuffixFindL(std::vector<Suf> const& suf, std::string const& base, std::string const& wht)
{
	int l = -1;
	int r = suf.size();
	while (l < r - 1)
	{
		auto m = (l + r) / 2;
		auto res = SmartSubstr(base, suf[m].ind, wht.size()).compare(wht);
		if (res < 0)
			l = m;
		else
			r = m;
	}
	if (r >= suf.size() || SmartSubstr(base, suf[r].ind, wht.size()) != wht)
		return -1;
	return r;
}

int SuffixFindR(std::vector<Suf> const& suf, std::string const& base, std::string const& wht)
{
	int l = 0;
	int r = suf.size();
	while (l < r - 1)
	{
		auto m = (l + r) / 2;
		auto res = SmartSubstr(base, suf[m].ind, wht.size()).compare(wht);
		if (res <= 0)
			l = m;
		else
			r = m;
	}
	if (l == suf.size() || SmartSubstr(base, suf[l].ind, wht.size()) != wht)
		return -1;
	return l;
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

	std::string str;
	std::getline(cin, str);
	int num;
	cin >> num;
	int s1 = str.size();
	str += str;

	auto suff = BuildSuffixArray(str);
	auto lcp = BuildLCP(str, suff);

	int ans = -1;

	for (int i = 0; i < suff.size(); i++)
		if (suff[i].ind > s1)
			continue;
		else if (i < lcp.size() && lcp[i] >= s1)
			continue;
		else if (--num == 0)
		{
			ans = suff[i].ind;
			break;
		}

	if (ans == -1)
	{
		cout << "IMPOSSIBLE\n";
		return 0;
	}

	std::cout
		<< std::string_view(str.c_str() + ans, s1 - ans)
		<< std::string_view(str.c_str(), ans)
		<< std::endl
		;

	return 0;
}