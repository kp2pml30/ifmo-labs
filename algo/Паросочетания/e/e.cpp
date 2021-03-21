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
#include <bitset>

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
3 2 3 2
..
..
..

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

	constexpr std::size_t RSIZE = 128 + 64;

	int n, m, a, b;
	cin >> n >> m >> a >> b;

	// if (m >= RSIZE)
	// 	throw "up";
	// 
	// if (a < 0 || b < 0)
	// 	throw "up";

	size_type cntfree = 0;

	std::vector<std::bitset<RSIZE>> rows(n, false);

	for (int i = 0; i < n; i++)
	{
		std::string line;
		std::getline(cin, line);
		if (line.empty())
		{
			i--;
			continue;
		}
		if (line.size() != m)
			throw "up";
		for (int j = 0; j < m; j++)
			if (line[j] == '*')
			{
				rows[i][j] = true;
				cntfree++;
			}
			else
			{
				if (line[j] != '.')
					throw "up";
				rows[i][j] = false;
			}
	}

	if (b * 2 <= a)
	{
		cout << cntfree * b << std::endl;
		// throw "up";
		return 0;
	}

#if 1
	size_type lsize = (n * m + 1) / 2 + 5;

	struct AutoIncr
	{
		int val;

		AutoIncr()
		{
			static int counter = 0;
			val = counter++;
		}

		operator int()
		{
			return val;
		}
	};

	std::map<std::pair<int, int>, AutoIncr> odds;

	auto getInd = [&odds](int i, int j) {
		return odds[{i, j}];
	};

	std::vector<std::vector<size_type>> lg(lsize);

	std::vector<std::pair<char, char>> coordByInd;
	coordByInd.reserve(lsize);

	for (int i = 0; i < n; i++)
	for (int j = i % 2; j < m; j += 2)
	{
		if (!rows[i][j])
			continue;
		auto ind = coordByInd.size();
		coordByInd.emplace_back(i, j);
		if (i > 0 && rows[i - 1][j])
			lg[ind].push_back(getInd(i - 1, j));
		if (j > 0 && rows[i][j - 1])
			lg[ind].push_back(getInd(i, j - 1));

		if (i < n - 1 && rows[i + 1][j])
			lg[ind].push_back(getInd(i + 1, j));
		if (j < m - 1 && rows[i][j + 1])
			lg[ind].push_back(getInd(i, j + 1));
	}

	size_type rsize = odds.size();

	std::vector<bool> visited;
	std::vector<size_type> answer(rsize, -1);

	std::function<bool(size_type)> kuhn_impl = [&](size_type v) {
		if (visited[v])
			return false;
		visited[v] = true;
		for (auto const& to : lg[v])
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

	std::int64_t doubles = 0;
	for (size_type i = 0; i < answer.size(); i++)
		if (answer[i] != (size_type)-1)
			doubles++;

	std::int64_t singles = cntfree - doubles * 2;

	if (singles < 0)
		throw "up";


	cout << doubles * a + singles * b << std::endl;
#endif
	return 0;
}