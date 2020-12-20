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
4 5
1 2
1 3
2 3
2 4
3 4
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
#endif
 
using uint = std::uint32_t;
using size_type = std::uint32_t;
 
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
 
using Poly = std::vector<int>;
 
void MergePolyInPlace(Poly& l, Poly const& r)
{
    l.resize(std::max(l.size(), r.size()));
    for (size_type i = 0; i < r.size(); i++)
        l[i] += r[i];
}
 
void Dfs(Poly& ansAccum, std::vector<std::set<size_type>>& vec, size_type n, int sign = 1, size_type startfrom = 0)
{
TAILREC:
    for (size_type i = startfrom; i < vec.size(); i++)
        if (!vec[i].empty())
        {
            startfrom = i;
 
            auto iter = vec[i].begin();
            auto val = *iter;
 
            {
                // constuct new graph
                std::vector<std::set<size_type>> nw(vec.size());
                for (size_type j = startfrom; j < vec.size(); j++)
                {
                    if (j == val)
                    {
                        for (auto const& a : vec[j])
                            if (a != i)
                                nw[i].emplace(a);
                        continue;
                    }
                    nw[j] = vec[j];
                    if (nw[j].erase(val) && j != i)
                        nw[j].emplace(i);
                }
                Dfs(ansAccum, nw, n - 1, -1 * sign, startfrom);
            }
 
            // remove graph to make new
            vec[i].erase(iter);
            vec[val].erase(i);
 
            goto TAILREC;
        }
    // no edges
    Poly pol(n + 1);
    pol.back() = sign;
    MergePolyInPlace(ansAccum, pol);
}
 
int main(void)
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n, m;
 
    cin >> n >> m;
 
    std::vector<std::set<size_type>> verts(n);
 
    for (size_type i = 0; i < m; i++)
    {
        size_type a, b;
        cin >> a >> b;
        a--;
        b--;
        verts[a].emplace(b);
        verts[b].emplace(a);
    }
 
    Poly ans;
    Dfs(ans, verts, n);
 
    while (!ans.empty() && ans.back() == 0)
        ans.pop_back();
    std::reverse(ans.begin(), ans.end()); // god forgive me
    std::cout << ans.size() - 1 << '\n';
    for (auto const& a : ans)
        std::cout << a << ' ';
 
    std::cout << std::endl;
 
    return 0;
}