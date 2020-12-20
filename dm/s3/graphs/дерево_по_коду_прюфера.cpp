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
auto cin = std::stringstream(R"delim(
5
2 3 3
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
 
    std::vector<size_type>
        pruf,
        deg(n, 0);
 
    for (size_type _ = 0; _ < n - 2; _++)
    {
        size_type a, b;
        cin >> a;
        a--;
        deg[a]++;
        pruf.emplace_back(a);
    }
 
    std::set<size_type> queue;
 
    for (size_type i = 0; i < n; i++)
        if (deg[i] == 0)
            queue.emplace(i);
 
    for (size_type i = 0; i < n - 2; i++)
    {
        if (queue.empty())
            throw "Bad";
        auto lv = queue.begin();
        auto a = *lv;
        queue.erase(lv);
 
        auto cur = pruf[i];
        std::cout << a + 1 << ' ' << cur + 1 << '\n';
        deg[cur]--;
        if (deg[cur] == 0)
            queue.emplace(cur);
    }
 
    if (queue.size() != 2)
        throw "down";
    {
        auto it = queue.begin();
        std::cout << *it + 1 << ' ';
        ++it;
        std::cout << *it + 1 << std::endl;
    }
 
    return 0;
}