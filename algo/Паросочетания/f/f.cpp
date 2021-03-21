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
4
1 0 3 0
1 1 3 1
1 2 3 2
2 10 2 -10


)delim");
using std::cout;
#else
using std::cin;
using std::cout;
// static auto cin = std::ifstream("matching.in");
// static auto cout = std::ofstream("matching.out");
#endif

using uint = std::uint32_t;
using size_type = std::int64_t;;

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

	iterator begin() const noexcept { return {b, s}; }
	iterator end() const noexcept { return {e, s}; }
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

void query()
{
	int n;
	cin >> n;

	struct segm
	{
		int i;
		int j1, j2;

		bool intersects(segm const& r) const noexcept
		{
			auto const& l = *this;
			return
				l.i >= r.j1 && l.i <= r.j2 &&
				r.i >= l.j1 && r.i <= l.j2;
		}
	};

	std::vector<segm>
		vert, hor;

	for (auto const& a : Range(n))
	{
		int x1, x2, y1, y2;
		cin >> x1 >> y1 >> x2 >> y2;
		if (x1 > x2)
			std::swap(x1, x2);
		if (y1 > y2)
			std::swap(y1, y2);
		if (x1 == x2)
			vert.push_back({x1, y1, y2});
		else
			hor.push_back({y1, x1, x2});
	}

	int lsize = vert.size(), rsize = hor.size();

	auto
		l_range = Range(lsize),
		r_range = Range(rsize);

	std::vector<std::unordered_set<int>> l2rgraph(lsize);
	for (auto const& l : l_range)
	for (auto const& r : r_range)
		if (vert[l].intersects(hor[r]))
			l2rgraph[l].emplace(r);

	// for (auto& a : l2rgraph)
	// 	a = inverseSet<std::unordered_set<int>>(r_range, a);

	std::vector<int> r2l_matching(rsize, -1);

	// kuhn
	{
		std::vector<bool> visited;
		std::function<bool(size_type)> kuhn_impl = [&](size_type v) {
			if (visited[v])
				return false;
			visited[v] = true;
			for (auto const& to : l2rgraph[v])
				if (r2l_matching[to] == (size_type)-1
					|| kuhn_impl(r2l_matching[to]))
				{
					r2l_matching[to] = v;
					return true;
				}
			return false;
		};
		auto kuhn = [&](size_type v) {
			visited.assign(lsize, false);
			kuhn_impl(v);
		};

		for (size_type i = 0; i < lsize; i++)
			kuhn(i);
	}

	std::unordered_set<int> l_in_matching;

	for (size_type i = 0; i < r2l_matching.size(); i++)
		if (r2l_matching[i] != (size_type)-1)
		{
			l2rgraph[r2l_matching[i]].erase(i);
			l_in_matching.emplace(r2l_matching[i]);
		}

	std::unordered_set<int> lminus(l_range.begin(), l_range.end()), rplus;

	std::function<void(int)> ldfs, rdfs;

	std::unordered_set<int> l_visited, r_visited;

	ldfs = [&](int v) {
		if (l_visited.count(v))
			return;
		l_visited.emplace(v);
		lminus.erase(v);
		for (auto const& u : l2rgraph[v])
			rdfs(u);
	};

	rdfs = [&](int v) {
		if (r_visited.count(v))
			return;
		r_visited.emplace(v);
		rplus.emplace(v);
		if (r2l_matching[v] != (size_type)-1)
			ldfs(r2l_matching[v]);
	};

	for (auto const& a : l_range)
		if (!l_in_matching.count(a))
			ldfs(a);

	auto lans = inverseSet<std::set<int>>(l_range, lminus);
	auto rans = inverseSet<std::set<int>>(r_range, rplus);

	cout << lans.size() + rans.size() << '\n';
#if 0
	cout << lans.size() << ' ' << rans.size() << '\n';
	for (auto const& a : lans)
		cout << a + 1 << ' ';
	cout << '\n';
	for (auto const& a : rans)
		cout << a + 1 << ' ';
	cout << "\n\n";
#endif
}

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	query();

	cout << std::flush;

	return 0;
}