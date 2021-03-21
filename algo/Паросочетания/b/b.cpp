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
3 2 4
1 2 3
1 2
1 1
2 1
2 2
3 2

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

using graph_side = std::vector<std::vector<size_type>>;

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

auto makeOrder(std::vector<size_type> const& w)
{
	std::vector<size_type> order(w.size());
	std::iota(order.begin(), order.end(), 0);
	std::sort(order.begin(), order.end(), [&w](size_type a, size_type b) { return w[a] > w[b]; });
	return order;
};

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	size_type a_size, b_size, e;

	cin >> a_size >> b_size >> e;

	std::vector<size_type> a_w(a_size), b_w(b_size);
	for (size_type i = 0; i < a_size; i++)
		cin >> a_w[i];
	for (size_type i = 0; i < b_size; i++)
		cin >> b_w[i];

	graph_side a_graph(a_size), b_graph(b_size);

	std::map<std::pair<size_type, size_type>, int> edgeNum;

	for (size_type i = 0; i < e; i++)
	{
		size_type f, t;
		cin >> f >> t;
		f--;
		t--;
		a_graph[f].emplace_back(t);
		b_graph[t].emplace_back(f);
		edgeNum[{f, t}] = i;
	}

	// graph_side a_graph_n(a_size), b_graph_n(b_size);
	std::unordered_set<size_type> a_used, b_used;
	{
		auto ord = makeOrder(a_w);
		auto edg = kuhn(a_graph, b_size, ord);
		for (auto const& a : edg)
			a_used.emplace(a.first);
	}
	{
		auto ord = makeOrder(b_w);
		auto edg = kuhn(b_graph, a_size, ord);
		for (auto const& a : edg)
			b_used.emplace(a.first);
	}
	std::vector<std::pair<size_type, size_type>> answer = [&]() {
		graph_side a_new(a_size);
		for (int i = 0; i < a_graph.size(); i++)
		{
			if (a_used.count(i) == 0)
				continue;
			for (auto const& b : a_graph[i])
				if (b_used.count(b) != 0)
					a_new[i].emplace_back(b);
		}
		return kuhn(a_new, b_size, makeOrder(a_w));
	}();

	std::int64_t answer_w = 0;

	for (auto const& a : answer)
		answer_w += a_w[a.first] + b_w[a.second];
	cout << answer_w << '\n' << answer.size() << '\n';
	for (auto const& a : answer)
	{
		auto e = edgeNum.find(a);
		if (e == edgeNum.end())
			throw "up";
		cout << e->second + 1 << ' ';
	}
	cout << std::endl;

	return 0;
}