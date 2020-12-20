// no dont look

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

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(a````
1
2 3 4 5
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
#endif

using uint = std::uint32_t;
using size_type = std::uint32_t;

using Str = std::vector<char>;

int main(void)
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	std::string s;

	std::getline(cin, s);
	std::vector<char> chars(s.size());
	for (int i = 0; i < s.size(); i++)
		chars[i] = s[i] - 'a' + 1;

	size_type M;
	cin >> M;
	for (size_type i = 0; i < M; i++)
	{
		size_type a, b, c, d;
		cin >> a >> b >> c >> d;
		a--; b--;
		c--; d--;
		int n = b - a;
		bool bad = false;
		if (b - a != d - c)
			bad = true;
		else if (a == c)
			;
		else for (int i = 0; i <= n; i++)
			if (chars[a + i] != chars[c + i])
			{
				bad = true;
				break;
			}

		if (bad)
			cout << "No\n";
		else
			cout << "Yes\n";
	}

	return 0;
}