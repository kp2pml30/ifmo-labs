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
3 4
1 2 3 4 0
2 3 0
3 4 0
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

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	size_type a, b;

	cin >> a >> b;
	std::vector<std::vector<size_type>> A(a);
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
			A[i].emplace_back(to);
			m++;
		}
	}

	std::vector<bool> visited;
	std::vector<size_type> answer(b, -1);

	std::function<bool(size_type)> kuhn_impl = [&](size_type v) {
		if (visited[v])
			return false;
		visited[v] = true;
		for (auto const& to : A[v])
			if (answer[to] == (size_type)-1
				|| kuhn_impl(answer[to]))
			{
				answer[to] = v;
				return true;
			}
		return false;
	};
	auto kuhn = [&](size_type v) {
		visited.assign(a, false);
		kuhn_impl(v);
	};

	for (size_type i = 0; i < a; i++)
		kuhn(i);
	std::vector<std::pair<size_type, size_type>> answer_edges;
	for (size_type i = 0; i < answer.size(); i++)
		if (answer[i] != (size_type)-1)
			answer_edges.emplace_back(answer[i] + 1, i + 1);
	cout << answer_edges.size() << '\n';
	for (auto const& a : answer_edges)
		cout << a.first << ' ' << a.second << '\n';
	cout << std::flush;
	return 0;
}