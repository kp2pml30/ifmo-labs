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
#include <variant>
#include <numeric>

#ifdef _DEBUG
static auto cin = std::stringstream(R"delim(
5
7 10 5 3 7 
10 6 6 10 9 
7 7 7 5 9 
5 1 4 7 7 
5 10 6 5 6 


)delim");
using std::cout;
#else
using std::cin;
using std::cout;
// static auto cin = std::ifstream("matching.in");
// static auto cout = std::ofstream("matching.out");
#endif

using uint = std::uint32_t;
using size_type = std::int64_t;
using weight_t = std::int64_t;

template<typename T>
class Range
{
private:
	T b, e, s;
public:
	struct iterator
	{
		using iterator_category = std::input_iterator_tag;
		using value_type = T;
		using reference = value_type const&;
		using pointer = value_type const*;
		using difference_type = T;
		T b, s;

		T operator*() const noexcept { return b; }
		T const* operator->() const noexcept { return &b; }
		bool operator!=(iterator const& r) const noexcept
		{
			return b < r.b;
		}

		iterator& operator++() noexcept
		{
			b += s;
			return *this;
		}
		iterator operator++(int) noexcept
		{
			auto old = *this;
			b += s;
			return old;
		}

		T operator-(iterator const& r) const noexcept
		{
			return b - r.b;
		}
	};
	Range(T const& b, T const& e, T const& s)
		: b(b)
		, e(e)
		, s(s)
	{}

	Range(T const& b, T const& e)
		: Range(b, e, 1)
	{}

	Range(T const& e)
		: Range(0, e)
	{}

	iterator begin() const noexcept { return { b, s }; }
	iterator end() const noexcept { return { e, s }; }
};

template<typename T> Range(T)->Range<T>;
template<typename T> Range(int, T)->Range<T>;
template<typename T> Range(T, T)->Range<T>;
template<typename T> Range(T, T, T)->Range<T>;
template<typename T> Range(int, T, int)->Range<T>;

template<typename Ret, typename C1, typename C2>
Ret inverseSet(C1 const& range, C2 const& map)
{
	Ret ret;
	for (auto const& a : range)
		if (map.count(a) == 0)
			ret.emplace(a);
	return ret;
}

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	int n;

	cin >> n;

	constexpr weight_t winf = 1'000'000'000, wpreinf = winf - 5'000'000;

	std::vector<std::vector<weight_t>> matr(n + 1, std::vector<weight_t>(n + 1, wpreinf));

	for (auto const& row : Range(n))
		for (auto const& col : Range(n))
		{
			int w;
			cin >> w;
			matr[row + 1][col + 1] = w;
		}

	auto rsize = n;
	auto lsize = n;

	// code from prev lab >_<
	{
		// potentials
		std::vector<std::int64_t> u(lsize + 1, 0), v(rsize + 1, 0);
		std::vector<int> matching(rsize + 1, 0); // matching
		std::vector<int> mins_loc(rsize + 1, 0); // mins where
		std::vector<bool> used;
		for (int i = 1; i <= lsize; i++)
		{
			matching[0] = i;
			int j0 = 0;
			std::vector<std::int64_t> min_v(rsize + 1, winf); // helper mins
			used.assign(rsize + 1, false);
			while (true)
			{
				used[j0] = true;
				int i0 = matching[j0];
				int
					delta = winf,
					j1;
				for (int j = 1; j <= rsize; j++)
				{
					if (used[j])
						continue;
					auto cur = matr[i0][j] - u[i0] - v[j];
					if (cur < min_v[j])
					{
						min_v[j] = cur;
						mins_loc[j] = j0;
					}
					if (min_v[j] < delta)
					{
						delta = min_v[j];
						j1 = j;
					}
				}
				if (delta == winf)
					throw "up";
				for (int j = 0; j <= rsize; j++)
					if (used[j])
					{
						u[matching[j]] += delta;
						v[j] -= delta;
					}
					else
					{
						min_v[j] -= delta;
					}
				j0 = j1;
				if (matching[j0] == 0)
					break;
			}
			while (true)
			{
				auto mloc = mins_loc[j0];
				matching[j0] = matching[mloc];
				j0 = mloc;
				if (!j0)
					break;
			}
		}

		std::vector<std::pair<int, int>> edges_ans;
		std::int64_t weight_accum = 0;

		for (int j = 1; j <= rsize; ++j)
		{
			auto l = matching[j];
			auto r = j;
			if (l == 0 || r == 0 || matr[l][r] == wpreinf)
				continue;
			std::int64_t w = matr[l][r];
			weight_accum += w;
			edges_ans.emplace_back(l, r);
		}

		if (edges_ans.size() != n)
			throw "up";
		cout << weight_accum << '\n';

#if 1
		for (auto const& a : edges_ans)
			cout << a.first << ' ' << a.second << '\n';
#else
		std::map<int, int> eolymp;
		for (auto const& a : edges_ans)
			eolymp[a.first] = a.second;
		for (auto const& a : eolymp)
			cout << a.second << ' ';
		cout << '\n';
#endif
	}
	cout << std::flush;

	return 0;
}