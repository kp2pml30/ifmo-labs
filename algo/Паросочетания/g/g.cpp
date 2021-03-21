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
2 2 1
1
1 3
1
2

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

using graph_side = std::vector<std::unordered_set<size_type>>;

using weight_t = bool;

std::vector<std::pair<size_type, size_type>> kuhn(graph_side const& a_graph, size_type b_size)
{
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

	for (int i = 0; i < a_graph.size(); i++)
		kuhn(i);
	std::vector<std::pair<size_type, size_type>> answer_edges;
	for (size_type i = 0; i < answer.size(); i++)
		if (answer[i] != (size_type)-1)
			answer_edges.emplace_back(answer[i], i);
	return answer_edges;
}

[[noreturn]] void answerNO()
{
	cout << "NO" << std::endl;
	exit(0);
}

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	size_type a_size, b_size, double_limit;

	cin >> a_size >> b_size >> double_limit;

	auto setMaker = [](int limit) {
		std::unordered_set<size_type> set;
		for (int i = 0; i < limit; i++)
			set.emplace(i);
		return set;
	};

	graph_side
		a_graph(a_size, setMaker(b_size + a_size - double_limit)),
		b_graph(b_size, setMaker(a_size + b_size - double_limit));

	a_graph.resize(a_size + b_size - double_limit, setMaker(b_size));
	b_graph.resize(a_size + b_size - double_limit, setMaker(a_size));

	// read can't
	{
		int q;
		cin >> q;
		for (int i = 0; i < q; i++)
		{
			int a, b;
			cin >> a >> b;
			a--;
			b = b - 1 - a_size;
			a_graph[a].erase(b);
			b_graph[b].erase(a);
		}
	}

	// read no singles
	{
		int q;
		cin >> q;
		for (int i = 0; i < q; i++)
		{
			int j;
			cin >> j;
			j--;
			if (j >= a_size)
			{
				j -= a_size;
				for (int rem = a_size; rem < a_graph.size(); rem++)
				{
					b_graph[j].erase(rem);
					a_graph[rem].erase(j);
				}
			}
			else
			{
				for (int rem = b_size; rem < b_graph.size(); rem++)
				{
					a_graph[j].erase(rem);
					b_graph[rem].erase(j);
				}
			}
		}
	}

	auto answer = kuhn(a_graph, b_graph.size());

	if (answer.size() != a_graph.size())
	{
		cout << "NO" << std::endl;
		return 0;
	}

	cout << "YES\n";
	for (auto const& a : answer)
		if (a.first < a_size && a.second < b_size)
			cout << a.first + 1 << ' ' << a.second + a_size + 1 << '\n';
	cout << std::flush;

	return 0;
}