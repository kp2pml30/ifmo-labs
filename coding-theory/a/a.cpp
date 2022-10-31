#include <cstddef>
#include <functional>
#include <iostream>
#include <bitset>
#include <string>
#include <tuple>
#include <utility>
#include <vector>
#include <ranges>
#include <numeric>
#include <cassert>
#include <map>
#include <algorithm>
#include <sstream>
#include <string_view>
#include <array>
#include <forward_list>

#define let auto const

#ifdef _DEBUG

auto cin = std::stringstream(R"delim(8 4
1 1 1 1 1 1 1 1
1 1 1 1 0 0 0 0
1 1 0 0 1 1 0 0
1 0 1 0 1 0 1 0
Encode 1 0 0 0
Decode -1.0 1.0 1 1 1 1 1 1.5
Decode -10 1 1 1 1 1 1 1
Simulate 3 100000 100
Simulate 4 100000 100
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
#endif

constexpr auto SHOW_DBG = true;

#define DBG if constexpr (SHOW_DBG)
#define NOP

struct endl_t {} endl;

std::ostream& operator<<(std::ostream& o, endl_t)
{
	o << '\n';
	return o;
}

/* content */

class Vec : public std::vector<bool> {
public:
	using std::vector<bool>::vector;
};

Vec operator+(Vec const& l, Vec const& r) noexcept
{
	auto ret = Vec(l.size());
	for (size_t i = 0; i < l.size(); i++)
		ret[i] = l[i] ^ r[i];
	return ret;
}

Vec operator*(Vec const& l, Vec const& r) noexcept
{
	auto ret = Vec(l.size());
	for (size_t i = 0; i < l.size(); i++)
		ret[i] = l[i] & r[i];
	return ret;
}

Vec& operator*=(Vec& l, Vec const& r) noexcept
{
	l = l * r;
	return l;
}

Vec& operator+=(Vec& l, Vec const& r) noexcept
{
	l = l + r;
	return l;
}

using Mat = std::vector<Vec>;

void printMat(size_t n, Mat const& m)
{
	for (let& r : m)
		{
			for (size_t i = 0; i < n; i++)
				cout << r[i] << ' ';
			cout << endl;
		}
}

void toSpan(size_t n, Mat& m)
{
	for (size_t s = 0; s < m.size(); s++)
	{
		let ini = std::numeric_limits<decltype(s)>::max();
		auto fst = ini;
		for (auto i = s; i != m.size(); i++)
			if (m[i][s])
				if (fst == ini)
				{
					std::swap(m[i], m[s]);
					fst = s;
				}
				else
				{
					m[i] += m[fst];
				}
	}

	auto active = std::vector<int>(m.size());
	for (size_t s = 0; s < m.size(); s++)
		active[s] = (int)(m.size()-1-s);

	int col = n-1;
	while (active.size() > 0)
	{
		for (size_t i = 0; i < active.size(); i++)
			if (let& row = m[active[i]]; row[col])
			{
				for (size_t j = i+1; j < active.size(); j++)
					if (auto& row2 = m[active[j]]; row2[col])
						row2 += row;
				active.erase(std::next(active.begin(), i));
				break;
			}
		col--;
		assert(col >= 0);
	}
}

template<typename T>
std::vector<T> intersectSorted(std::vector<T> const& l, std::vector<T> const& r)
{
	auto res = std::vector<T>();
	size_t pl = 0;
	size_t pr = 0;
	while (pl < l.size() && pr < r.size())
	{
		if (l[pl] == r[pr])
		{
			res.emplace_back(l[pl]);
			pl++;
			pr++;
		}
		else if (l[pl] < r[pr])
		{
			pl++;
		}
		else
		{
			pr++;
		}
	}
	return res;
}

template<typename T>
std::vector<T> differenceSorted(std::vector<T> const& l, std::vector<T> const& r)
{
	auto res = std::vector<T>();
	size_t pl = 0;
	size_t pr = 0;
	while (pl < l.size() && pr < r.size())
	{
		if (l[pl] == r[pr])
		{
			pl++;
			pr++;
		}
		else if (l[pl] < r[pr])
		{
			res.emplace_back(l[pl]);
			pl++;
		}
		else
		{
			res.emplace_back(r[pr]);
			pr++;
		}
	}
	return res;
}

template<typename T>
std::vector<T> unionSorted(std::vector<T> const& l, std::vector<T> const& r)
{
	auto res = std::vector<T>();
	size_t pl = 0;
	size_t pr = 0;
	while (pl < l.size() && pr < r.size())
	{
		if (l[pl] == r[pr])
		{
			pr++;
		}
		else if (l[pl] < r[pr])
		{
			res.emplace_back(l[pl]);
			pl++;
		}
		else
		{
			res.emplace_back(r[pr]);
			pr++;
		}
	}
	while (pl < l.size())
	{
		res.emplace_back(l[pl]);
		pl++;
	}
	while (pr < r.size())
	{
		res.emplace_back(r[pr]);
		pr++;
	}
	return res;
}

struct DiffResult
{
	using T = size_t;
	static constexpr T NO = std::numeric_limits<T>::max();
	T ret = NO;
	T add = NO;
};

DiffResult smartDiff(std::vector<size_t> const& l, std::vector<size_t> const& r)
{
	auto res = DiffResult();
	size_t pl = 0;
	size_t pr = 0;

	while (pl < l.size() && pr < r.size())
	{
		let& le = l[pl];
		let& re = r[pr];
		if (le == re)
		{
			pl++;
			pr++;
		}
		else if (le < re)
		{
			assert(res.ret == DiffResult::NO);
			res.ret = le;
			pl++;
		}
		else
		{
			assert(res.add == DiffResult::NO);
			res.add = re;
			pr++;
		}
	}

	while (pl < l.size())
	{
		assert(res.ret == DiffResult::NO);
		res.ret = l[pl];
		pl++;
	}

	while (pr < r.size())
	{
		assert(res.add == DiffResult::NO);
		res.add = r[pr];
		pr++;
	}

	return res;
}

struct TrellisNode
{
	TrellisNode* to[2] = {};
};

class Trellis
{
public:
	TrellisNode* alloc()
	{
		if (idxInPool >= pool.front().size())
		{
			pool.emplace_front();
			idxInPool = 0;
		}
		return &pool.front()[idxInPool++];
	}

	std::vector<std::map<Vec, TrellisNode*>> layers;
private:
	std::forward_list<std::array<TrellisNode, 64>> pool = {{}};
	size_t idxInPool = 0;
};

int main()
{
	size_t n, k;
	cin >> n >> k;

	auto G = Mat(k, Vec(n));

	//==== read matrix
	for (let i : std::views::iota((decltype(k))0, k))
		for (let j : std::views::iota((decltype(n))0, n))
		{
			int a;
			cin >> a;
			G[i][j] = a;
		}

	DBG {
		cout << "G\n";
		printMat(n, G);
	}

	auto G0 = G;

	//==== span form
	toSpan(n, G);

	DBG {
		cout << "G span\n";
		printMat(n, G);
	}

	auto G0T = Mat(n ,Vec(k));
	for (let i : std::views::iota((size_t)0, k))
		for (let j : std::views::iota((size_t)0, n))
			G0T[j][i] = G0[i][j];

	//==== calc v_i
	auto activeNodes = std::vector<std::vector<size_t>>(n+1);
	{
		auto firsts = std::vector<size_t>();
		auto lasts = std::vector<size_t>();
		firsts.reserve(k);
		lasts.reserve(k);
		for (size_t i = 0; i < k; i++)
		{
			let& row = G[i];
			auto ok = false;
			for (size_t j = 0; j < n; j++)
				if (row[j])
				{
					firsts.emplace_back(j);
					ok = true;
					break;
				}
			assert(ok);
			ok = false;
			for (size_t j = n; j > 0; j--)
				if (row[j-1])
				{
					lasts.emplace_back(j-1);
					ok = true;
					break;
				}
			assert(ok);
		}

		assert(firsts.size() == lasts.size());
		for (size_t i = 0; i < firsts.size(); i++)
			for (size_t j = i+1; j < firsts.size(); j++)
			{
				assert(firsts[i] != firsts[j]);
				assert(lasts[i] != lasts[j]);
			}

		for (size_t i = 0; i < n; i++)
		{
			auto& row = activeNodes[i+1];
			for (size_t j = 0; j < firsts.size(); j++)
				if (firsts[j] <= i && i < lasts[j])
					row.emplace_back(j);
		}

		DBG cout << "V_i: ";
		for (let& a : activeNodes)
			cout << (1 << a.size()) << ' ';
		cout << endl;
	}

	//==== build lattice
	auto pLayerId = [](std::ostream& o, Vec const& l) -> decltype(auto) {
		for (let i : l)
			o << i;
		return o;
	};


	auto trellis = std::vector<std::map<Vec, std::pair<Vec const*, Vec const*>>>(n+1);

	auto printGraph = [&](){
		auto i = size_t(0);
		for (let& layer : trellis)
		{
			cout << i++ << endl;
			for (let& [k, v] : layer)
			{
				pLayerId(cout << "\t{", k) << "} -> [";

				if (v.first == nullptr)
					cout << "_";
				else
					pLayerId(cout, *v.first);

				cout << " ";

				if (v.second == nullptr)
					cout << "_";
				else
					pLayerId(cout, *v.second);

				cout << "]" << endl;
			}
		}
	};


	trellis[0][Vec()] = std::make_pair(nullptr, nullptr);
	for (let i : std::views::iota(size_t(0), n))
	{
		auto& last = trellis[i];
		auto& next = trellis[i+1];

		let& lastActive = activeNodes[i];
		let& nextActive = activeNodes[i+1];

		auto allSym = unionSorted(lastActive, nextActive);

		let sd = smartDiff(lastActive, nextActive);
		assert(sd.ret == DiffResult::NO || sd.add == DiffResult::NO);

		auto makeCopy = [&](Vec const& of) -> std::vector<Vec> {
			auto ret1 = Vec();
			auto ret2 = Vec();
			auto acti = size_t(0);
			auto wasAdd = false;
			while (acti < lastActive.size())
			{
				if (sd.add < lastActive[acti] && !wasAdd)
				{
					wasAdd = true;
					ret1.emplace_back(false);
					ret2.emplace_back(true);
				}
				if (lastActive[acti] != sd.ret)
				{
					ret1.emplace_back(of[acti]);
					ret2.emplace_back(of[acti]);
				}
				acti++;
			}
			if (!wasAdd && sd.add != DiffResult::NO)
			{
				wasAdd = true;
				ret1.emplace_back(false);
				ret2.emplace_back(true);
			}
			if (wasAdd)
				return {std::move(ret1), std::move(ret2)};
			else
				return {std::move(ret1)};
		};


		for (auto& [last_vals, last_dir] : last)
		{
			auto added = makeCopy(last_vals);
			auto ins = [&](Vec const& w, bool dig) {
				auto iter = next.emplace(
					std::piecewise_construct,
					std::forward_as_tuple(w),
					std::forward_as_tuple()
				).first;

				auto mem = (Vec const**)nullptr;
				if (dig)
					mem = &last_dir.second;
				else
					mem = &last_dir.first;
				assert(*mem == nullptr);
				*mem = &iter->first;
			};

			auto sum = false;
			for (size_t a = 0; a < lastActive.size(); a++)
				sum ^= G[lastActive[a]][i] & last_vals[a];

			ins(added[0], sum);
			if (sd.add != DiffResult::NO)
			{
				sum ^= G[sd.add][i];
				assert(added.size() == 2);
				ins(added[1], sum);
			}
		}

		//DBG printGraph();
	}

	DBG printGraph();


	//==== iterate commands
	{
		std::string s;
		std::getline(cin, s);

		while (!cin.eof())
		{
			std::getline(cin, s);
			if (s == "" || s == "\n")
				continue;
			auto handle = [&](std::string_view command, auto f) {
				auto view = std::string_view(s);
				if (view.substr(0, command.size()) != command)
					return false;
				auto ss = std::stringstream(s.substr(std::string("Encode ").size()));
				f(ss);
				return true;
			};
			auto fail = [](std::string_view err) -> bool {
				throw err;
			};

			false
				|| handle("Encode", [&](std::stringstream& s) {
					auto u = Vec(k);
					for (let i : std::views::iota((size_t)0, k))
					{
						int b;
						s >> b;
						u[i] = b;
					}
					for (let i : std::views::iota((size_t)0, n))
					{
						auto ve = G0T[i] * u;
						cout << std::reduce(ve.begin(), ve.end(), false, std::bit_xor<>{}) << ' ';
					}
					cout << endl;
				})
				|| handle("Decode", [&](std::stringstream& s) {
					auto f = std::vector<float>();
					for (let i : std::views::iota((size_t)0, n))
					{
						float b;
						s >> b;
						f.emplace_back(b);
					}

					for (auto& layer : trellis)
					{

					}
					cout << "TODO: DECODE" << endl;
				})
				|| fail("unknown command");
		}
	}

	return 0;
}
