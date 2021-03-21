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
auto cin = std::stringstream(R"delim(
2
2 2
1 2 0
1 2 0
3 2
1 2 0
2 0
1 2 0

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
	int lsize, rsize;

	cin >> lsize >> rsize;

	auto
		l_range = Range(lsize),
		r_range = Range(rsize);

	std::vector<std::unordered_set<int>> l2rgraph(lsize);
	for (int i = 0; i < lsize; i++)
	{
		while (true)
		{
			int to;
			cin >> to;
			if (to == 0)
				break;
			to--;
			l2rgraph[i].emplace(to);
		}
	}

	for (auto& a : l2rgraph)
		a = inverseSet<std::unordered_set<int>>(r_range, a);

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
	cout << lans.size() << ' ' << rans.size() << '\n';
	for (auto const& a : lans)
		cout << a + 1 << ' ';
	cout << '\n';
	for (auto const& a : rans)
		cout << a + 1 << ' ';
	cout << "\n\n";
}

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	int n;
	cin >> n;
	while (n-- > 0)
		query();

	cout << std::flush;

	return 0;
}