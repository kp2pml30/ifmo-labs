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
4
1 3 2 4
4 1 2 3 4
2 1 4
2 1 4
2 1 4
)delim");
using std::cout;
#else
// using std::cin;
// using std::cout;
static auto cin = std::ifstream("matching.in");
static auto cout = std::ofstream("matching.out");
#endif
 
using uint = std::uint32_t;
using size_type = std::int64_t;;
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n;
 
    cin >> n;
    std::vector<size_type> weights(n);
    for (size_type i = 0; i < n; i++)
        cin >> weights[i];
    std::vector<std::vector<size_type>> leftGraph(n);
    for (size_type i = 0; i < n; i++)
    {
        size_type cnt;
        cin >> cnt;
        leftGraph[i].reserve(cnt);
        for (size_type _ = 0; _ < cnt; _++)
        {
            size_type j;
            cin >> j;
            j--;
            leftGraph[i].emplace_back(j);
        }
    }
 
    std::vector<size_type> order(n);
    std::iota(order.begin(), order.end(), 0);
    std::sort(order.begin(), order.end(), [&](size_type l, size_type r) {
        return weights[l] > weights[r];
    });
 
    std::vector<bool> visited;
    std::vector<size_type> answer(n, -1);
    std::function<bool(size_type)> kuhn_impl = [&](size_type v) {
        if (visited[v])
            return false;
        visited[v] = true;
        for (auto const& to : leftGraph[v])
            if (answer[to] == (size_type)-1
                    || kuhn_impl(answer[to]))
            {
                answer[to] = v;
                return true;
            }
        return false;
    };
    auto kuhn = [&](size_type v) {
        visited.assign(n, false);
        kuhn_impl(v);
    };
 
    for (size_type i = 0; i < n; i++)
        kuhn(order[i]);
    std::vector<size_type> back(n, -1);
    for (size_type i = 0; i < n; i++)
        if (answer[i] != -1)
            back[answer[i]] = i;
    for (auto const& a : back)
        cout << a + 1 << ' ';
    cout << std::endl;
    return 0;
}