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
3
1 1
1 2
0 100
)delim");
using std::cout;
#else
// using std::cin;
// using std::cout;
static auto cin = std::ifstream("schedule.in");
static auto cout = std::ofstream("schedule.out");
#endif
 
using uint = std::uint32_t;
using size_type = std::uint64_t;;
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n;
 
    cin >> n;
    std::map<size_type, std::multiset<size_type, std::greater<>>> tasks;
    for (size_type i = 0; i < n; i++)
    {
        size_type d, w;
        cin >> d >> w;
        tasks[d].emplace(w);
    }
 
    std::map<size_type, size_type> tekken;
    size_type last = 0;
    std::uint64_t ans = 0;
 
    if (!tasks.empty() && tasks.begin()->first == 0)
    {
        ans += std::accumulate(tasks.begin()->second.begin(), tasks.begin()->second.end(), 0ULL);
        tasks.erase(tasks.begin());
    }
 
    for (auto const& stepped : tasks)
    {
        // put empty cells
        tekken[0] += stepped.first - last;
        last = stepped.first;
 
        for (auto iter = stepped.second.begin(); iter != stepped.second.end(); ++iter)
        {
            auto beg = tekken.begin();
            if (beg->first < *iter)
            {
                ans += beg->first;
                beg->second--;
                if (beg->second == 0)
                    tekken.erase(beg);
                tekken[*iter]++;
            }
            else
            {
                ans += std::accumulate(iter, stepped.second.end(), 0ULL);
                break;
            }
        }
    }
    cout << ans << std::endl;
    return 0;
}