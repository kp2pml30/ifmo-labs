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
 
#if defined(_DEBUG)
#   error PCMS IS BAD
#endif
 
#if defined(_DEBUG)
auto cin = std::stringstream(R"delim(
5
1 2
2 3
4 3
3 5
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
#endif
 
using uint = std::uint32_t;
using size_type = std::uint32_t;
 
int main(void)
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n;
 
    cin >> n;
 
    std::vector<std::set<size_type>> graph(n);
 
    for (size_type _ = 0; _ < n - 1; _++)
    {
        size_type a, b;
        cin >> a >> b;
        a--;
        b--;
        graph[a].emplace(b);
        graph[b].emplace(a);
    }
 
    std::set<size_type> queue;
 
    for (size_type i = 0; i < n; i++)
    {
        if (graph[i].empty())
            throw "not a tree";
        if (graph[i].size() == 1)
            queue.emplace(i);
    }
 
    size_type used = 0;
 
    while (true)
    {
        if (used == n - 2)
            break;
        if (queue.empty())
            throw "not a tree";
        auto currentit = queue.begin();
        size_type curind = *currentit;
        size_type frnt = *graph[curind].begin();
        std::cout << frnt + 1 << ' ';
        queue.erase(currentit);
        graph[frnt].erase(curind);
        if (graph[frnt].size() == 1)
            queue.emplace(frnt);
        used++;
    }
 
    std::cout << std::endl;
 
    return 0;
}