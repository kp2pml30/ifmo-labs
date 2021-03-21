#include <cassert>
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
2 2
1 2 0
2 0

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

using graph_side = std::vector<std::set<size_type>>;

auto kuhn(graph_side const& a_graph, size_type b_size, std::vector<size_type> const& order)
{
	assert(order.size() == a_graph.size());

	size_type a_size = a_graph.size();
	std::vector<bool> visited;
	std::vector<size_type> answer(b_size, -1);
	std::function<bool(size_type)> kuhn_impl = [&](size_type v) {
		if (visited[v])
			return false;
		visited[v] = true;
		for (auto const& to : a_graph[v])
			if (answer[to] == (size_type)-1
				|| kuhn_impl(answer[to]))
			{
				answer[to] = v;
				return true;
			}
		return false;
	};
	auto kuhn = [&](size_type v) {
		visited.assign(a_size, false);
		kuhn_impl(v);
	};

	for (auto const& i : order)
		kuhn(i);
	std::vector<std::pair<size_type, size_type>> answer_edges;
	for (size_type i = 0; i < answer.size(); i++)
		if (answer[i] != (size_type)-1)
			answer_edges.emplace_back(answer[i], i);
	return answer_edges;
}

auto makeOrder(graph_side const& g, std::vector<size_type> const& w)
{
	if (g.size() != w.size())
		throw "up";
	std::vector<size_type> order(g.size());
	std::iota(order.begin(), order.end(), 0);
	std::sort(order.begin(), order.end(), [&w](size_type a, size_type b) { return w[a] > w[b]; });
	return order;
};

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

#if 0
	size_type a_size, b_size, e;

	cin >> a_size >> b_size >> e;

	graph_side a_graph(a_size), b_graph(b_size);

	std::vector<size_type> a_w(a_size), b_w(b_size);
	for (size_type i = 0; i < a_size; i++)
		cin >> a_w[i];
	for (size_type i = 0; i < b_size; i++)
		cin >> b_w[i];

	for (auto const& a : a_w)
		if (a < 0)
			throw "up";
	for (auto const& a : b_w)
		if (a < 0)
			throw "up";

	struct AutoIncr
	{
	private:
		int val;
	public:
		AutoIncr()
		{
			static int counter = 0;
			val = counter++;
		}

		operator int() { return val; }
	};
	std::map<std::pair<size_type, size_type>, AutoIncr> edgeNum;

	for (size_type i = 0; i < e; i++)
	{
		size_type f, t;
		cin >> f >> t;
		f--;
		t--;
		a_graph[f].emplace(t);		b_graph[t].emplace(f);
		edgeNum[{f, t}];
	}

	auto a_order = makeOrder(a_graph, a_w);
	auto edges1 = kuhn(a_graph, b_size, a_order);

	auto b_order = makeOrder(b_graph, b_w);
	auto edges2 = kuhn(b_graph, a_size, b_order);

	graph_side a_new(a_size);
	for (auto const& i : edges1)
		a_new[i.first].emplace(i.second);
	for (auto const& i : edges2)
		a_new[i.second].emplace(i.first);

	auto answer = kuhn(a_new, b_size, a_order);
	std::sort(answer.begin(), answer.end(), [&edgeNum](auto a, auto b) { return edgeNum[a] < edgeNum[b]; });

	std::int64_t wans = 0;
	for (auto const& i : answer)
		wans += a_w[i.first] + b_w[i.second];

	cout << wans << '\n' << answer.size() << '\n';

	for (auto const& a : answer)
		cout << edgeNum[a] + 1 << ' ';
	cout << std::endl;
#else
	size_type a, b;

	cin >> a >> b;
	graph_side A(a);
	size_type m = 0;
	for (size_type i = 0; i < a; i++)
	{
		while (true)
		{
			int to;
			cin >> to;
			if (to == 0)
				break;
			to--;
			A[i].emplace(to);
			m++;
		}
	}
	std::vector<size_type> aw(a);
	for (auto& c : aw)
		c = rand() % 10000 - 5000;
	auto ans = kuhn(A, b, makeOrder(A, aw));
	cout << ans.size() << '\n';
	for (auto const& a : ans)
		cout << a.first+1 << ' ' << a.second+1 << '\n';
	cout << std::flush;
#endif
	return 0;
}