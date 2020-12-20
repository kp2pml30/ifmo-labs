// no dont look
 
#include <array>
#include <vector>
#include <iostream>
#include <algorithm>
#include <fstream>
#include <cstdint>
#include <cmath>
#include <sstream>
#include <map>
#include <functional>
#include <map>
#include <set>
#include <unordered_set>
#include <list>
 
#if defined(_DEBUG)
auto cin = std::stringstream(R"delim(
6
 
1
10
011
0110
10011
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
#endif
 
using uint = std::uint32_t;
using size_type = std::uint16_t;
 
std::pair<size_type, size_type> MakePair(size_type a, size_type b)
{
    if (a < b)
        return {a, b};
    return {b, a};
}
 
bool operator<(std::pair<size_type, size_type> const& l, std::pair<size_type, size_type> const& r)
{
    return l.first < r.first
        || l.first == r.first && l.second < r.second;
}
 
int main(void)
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n;
 
    cin >> n;
 
    std::vector<std::vector<bool>> graph(n, std::vector<bool>(n, false));
    std::unordered_set<size_type> used;
    std::list<size_type> ham_path = {0};
    std::unordered_set<size_type> possible;
 
    std::vector<std::vector<size_type>> edges2(n);
 
    {
        std::string str;
        std::getline(cin, str);
    }
 
    for (size_type i = 0; i < n; i++)
    {
        std::string str;
        std::getline(cin, str);
        for (size_type j = 0; j < i; j++)
            if (str[j] == '1')
            {
                graph[i][j] = graph[j][i] = true;
                edges2[i].emplace_back(j);
                edges2[j].emplace_back(i);
            }
    }
 
    auto ProcessVert = [&](size_type val) {
        used.emplace(val);
        for (auto const& a : edges2[val])
            if (used.count(a) == 0)
                possible.emplace(a);
    };
 
    ProcessVert(0);
 
CONT:
    while (!possible.empty())
    {
        for (auto const& a : edges2[ham_path.front()])
            if (possible.count(a))
            {
                possible.erase(a);
                ProcessVert(a);
                ham_path.push_front(a);
                goto CONT;
            }
        for (auto const& a : edges2[ham_path.back()])
            if (possible.count(a))
            {
                possible.erase(a);
                ProcessVert(a);
                ham_path.push_back(a);
                goto CONT;
            }
        auto beg = possible.begin();
        auto val = *beg;
        possible.erase(beg);
        ProcessVert(val);
 
        if (graph[val][ham_path.front()])
        {
            ham_path.push_front(val);
            continue;
        }
        if (graph[val][ham_path.back()])
        {
            ham_path.push_back(val);
            continue;
        }
 
        decltype(ham_path)::iterator
            e1 = ham_path.end(),
            e2 = ham_path.end(),
            ct = ham_path.end();
        bool needsReverse = false;
        for (auto it = ham_path.begin(); it != ham_path.end();)
        {
            auto nxt = std::next(it);
            if (graph[*it][ham_path.back()] && graph[*nxt][ham_path.front()])
            {
                e1 = it;
                e2 = nxt;
                if (ct == ham_path.end())
                    needsReverse = true;
                else
                {
                    needsReverse = false;
                    break;
                }
            }
            if (graph[*it][val])
                ct = it;
            it = nxt;
        }
        if (e1 == ham_path.end() || ct == ham_path.end())
            return 1;
        if (ct == e1)
            needsReverse = false;
        if (needsReverse)
        {
            ham_path.reverse();
            std::swap(e1, e2);
        }
 
        decltype(ham_path) cte1, e2end;
        cte1.splice(cte1.begin(), ham_path, ct, e2);
        e2end.splice(e2end.begin(), ham_path, e2, ham_path.end());
        cte1.push_front(val);
 
        ham_path.reverse();
        ham_path.splice(ham_path.end(), e2end);
        cte1.reverse();
        ham_path.splice(ham_path.end(), cte1);
    }
 
    // to cycle
    if (!graph[ham_path.front()][ham_path.back()])
        for (auto it = ham_path.begin(); it != ham_path.end();)
        {
            auto nxt = std::next(it);
            if (graph[*it][ham_path.back()] && graph[*nxt][ham_path.front()])
            {
                std::reverse(ham_path.begin(), nxt);
                break;
            }
            it = nxt;
        }
 
    for (auto const& a : ham_path)
        cout << a + 1 << ' ';
    std::cout << std::endl;
 
    return 0;
}