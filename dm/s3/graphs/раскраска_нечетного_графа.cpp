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
3 2
1 3
3 2
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
 
size_type GetK(size_type a)
{
    return a / 2 * 2 + 1;
}
 
int main(void)
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n, m;
 
    cin >> n >> m;
 
    if (m * 2 == n * (n - 1))
    {
        std::cout << GetK(n) << '\n';
        for (size_type i = 0; i < n; i++)
            std::cout << i + 1 << '\n';
        return 0;
    }
 
    std::vector<std::vector<size_type>> wht(n);
 
    size_type maxdeg = 0;
 
    for (size_type i = 0; i < m; i++)
    {
        size_type a, b;
        cin >> a >> b;
        a--;
        b--;
        wht[a].emplace_back(b);
        wht[b].emplace_back(a);
        maxdeg = std::max(maxdeg, (size_type)wht[a].size());
        maxdeg = std::max(maxdeg, (size_type)wht[b].size());
    }
 
    if (m == n && n % 2 != 0)
    {
        bool ok = false;
        for (auto const& a : wht)
            if (a.size() != 2)
            {
                ok = true;
                break;
            }
        if (!ok)
        {
            std::cout << 3 << '\n' << 3 << '\n';
            for (size_type i = 0; i < n; i++)
                std::cout << (i % 2 + 1) << '\n';
            return 0;
        }
    }
 
    /*
    size_type gooddeg = maxdeg, startfrom = 0;
    for (size_type i = 0; i < n; i++)
        if (wht[i].size() < gooddeg)
        {
            gooddeg = wht[i].size();
            startfrom = 0;
            break;
        }
    */
 
    maxdeg = GetK(maxdeg);
 
    std::vector<std::set<size_type>> possible;
    {
        std::set<size_type> possible_base;
        for (size_type i = 0; i < maxdeg; i++)
            possible_base.emplace(i);
        possible.resize(n, possible_base);
    }
 
    std::vector<size_type> ans(n, 0);
 
    std::function<void(size_type cur)> func = [&](size_type cur) {
        if (ans[cur] != 0)
            return;
        if (possible[cur].empty())
            abort();
        auto val = *possible[cur].begin();
        ans[cur] = val + 1;
        possible[cur].clear();
        for (auto& a : wht[cur])
            possible[a].erase(val);
        for (auto const& a : wht[cur])
            func(a);
    };
 
    // func(startfrom);
 
    for (size_type i = 0; i < n; i++)
        func(i);
 
    std::cout << maxdeg << '\n';
    for (auto const& a : ans)
        std::cout << a << '\n';
 
    std::cout << std::endl;
 
    return 0;
}