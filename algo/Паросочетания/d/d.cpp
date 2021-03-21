#define _CRT_SECURE_NO_WARNINGS

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
#include <algorithm>

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
4 1
13:10 0 1
15:00 1 1
14:00 1 0
12:00 0 0

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

	int n;
	size_type v;

	cin >> n >> v;

	if (v < 0)
		throw "up";

	size_type lsize = n, rsize = lsize;

	std::vector<std::vector<size_type>> graphL(lsize);

	struct Event
	{
		size_type t;
		size_type x, y;
	};

	std::vector<Event> events;

	for (int i = 0; i < n; i++)
	{
		std::string line;
		std::getline(cin, line);
		if (line.empty())
		{
			i--;
			continue;
		}
		int h, m, x, y;
		if (sscanf(line.c_str(), "%d:%d %d %d", &h, &m, &x, &y) != 4)
			throw "up";
		float x1, y1;
		if (sscanf(line.c_str(), "%d:%d %f %f", &h, &m, &x1, &y1) != 4)
			throw "up";
		if (x != x1 || y != y1)
			throw "up";

		if (m >= 60 || m < 0 || h < 0 || h >= 24)
			throw "up";

		events.push_back({h * 60 + m, x, y});
	}

	std::sort(events.begin(), events.end(), [](Event const& a, Event const& b) { return a.t < b.t; });

	for (size_type i = 0; i < events.size(); i++)
	{
		auto const& e1 = events[i];
		for (size_type j = i + 1; j < events.size(); j++)
		{
			auto const& e2 = events[j];

			size_type dx = e2.x - e1.x;
			size_type dy = e2.y - e1.y;
			size_type dt = e2.t - e1.t;

			size_type maxdist = v * dt; // km/h * m = km * 60

			if (maxdist * maxdist < (dx * dx + dy * dy) * 60 * 60)
				continue;
			graphL[i].emplace_back(j);
		}
	}

	std::vector<size_type> answer(rsize, -1);
	{
		std::vector<bool> visited;
		std::function<bool(size_type)> kuhn_impl = [&](size_type v) {
			if (visited[v])
				return false;
			visited[v] = true;
			for (auto const& to : graphL[v])
				if (answer[to] == (size_type)-1
					|| kuhn_impl(answer[to]))
				{
					answer[to] = v;
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

	int ufoCount = 0;

	{
		std::vector<bool> visited(lsize, false);

		for (int i = 0; i < rsize; i++)
		{
			int j = i;
			while (!visited[j])
			{
				visited[j] = true;
				if (answer[j] == (size_type)-1)
					ufoCount++;
				else
					j = answer[j];
			}
		}
	}

	cout << ufoCount << std::endl;
	return 0;
}