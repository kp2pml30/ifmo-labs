// no dont look
 
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
 
#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
2 4
0
1 1
1 2
2 1 2
 
 
)delim");
using std::cout;
#else
// using std::cin;
// using std::cout;
static auto cin = std::ifstream("check.in");
static auto cout = std::ofstream("check.out");
#endif
 
using uint = std::uint32_t;
using size_type = std::uint16_t;
 
struct SetComparator
{
    bool operator()(std::set<size_type> const& a, std::set<size_type> const& b) const noexcept
    {
        if (a.size() < b.size())
            return false;
        if (a.size() > b.size())
            return true;
        return a < b;
    }
};
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n, m;
 
    cin >> n >> m;
    std::set<std::set<size_type>, SetComparator> sets;
    bool wasEmpty = false;
    for (int _ = 0; _ < m; _++)
    {
        size_type cnt;
        cin >> cnt;
        if (cnt == 0)
            wasEmpty = true;
        std::set<size_type> push;
        for (int i = 0; i < cnt; i++)
        {
            size_type p;
            cin >> p;
            push.emplace(p);
        }
        sets.emplace(std::move(push));
    }
    // first
    if (!wasEmpty)
        goto BADLAB;
    // second
    for (auto i1 = sets.begin(); i1 != sets.end(); ++i1)
    {
        // second
        {
            std::set<size_type> accum;
            std::function<bool(std::set<size_type>::iterator)> subsetgenerator = [&](std::set<size_type>::iterator iter) {
                if (iter == i1->end())
                {
                    if (sets.find(accum) == sets.end())
                        return false;
                    return true;
                }
                if (subsetgenerator(std::next(iter)) == false)
                    return false;
                auto brr = accum.emplace(*iter).first;
                if (subsetgenerator(std::next(iter)) == false)
                    return false;
                accum.erase(brr);
            };
            if (subsetgenerator(i1->begin()) == false)
                goto BADLAB;
        }
        for (auto i2 = std::next(i1); i2 != sets.end(); ++i2)
        {
            // third
            if (i1->size() > i2->size())
            {
                bool ok = false;
                auto copied = *i2;
                for (auto& elem : *i1)
                    if (i2->find(elem) == i2->end())
                    {
                        auto it = copied.emplace(elem).first;
                        if (sets.find(copied) != sets.end())
                        {
                            ok = true;
                            break;
                        }
                        copied.erase(it);
                    }
                if (!ok)
                    goto BADLAB;
            }
        }
    }
 
    cout << "YES\n";
    return 0;
BADLAB:
    cout << "NO\n";
    return 0;
}