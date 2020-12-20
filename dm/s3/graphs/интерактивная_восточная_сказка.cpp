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
#include <memory>
 
using std::cin;
using std::cout;
 
using uint = std::uint32_t;
using size_type = std::uint32_t;
 
std::pair<size_type, size_type> MakePair(size_type a, size_type b)
{
    if (a < b)
        return {a, b};
    return {b, a};
}
 
template<typename T, typename Y>
bool operator<(std::pair<T, Y> const& l, std::pair<T, Y> const& r)
{
    return l.first < r.first
        || l.first == r.first && l.second < r.second;
}
 
size_type CNT = 0;
 
struct MyCompare
{
    mutable std::map<std::pair<size_type, size_type>, bool> cache;
    bool operator()(size_type a, size_type b) const
    {
        if (a == b)
            return false;
        if (auto val = cache.find({a, b}); val != cache.end())
            return val->second;
        if (auto val = cache.find({b, a}); val != cache.end())
            return !val->second;
        CNT++;
        if (CNT >= 10'000)
            exit(1);
        cout << "1 " << a + 1 << ' ' << b + 1 << std::endl;
        std::string ans;
        cin >> ans;
        bool res = ans == "YES";
        cache[{a, b}] = res;
        return res;
    }
};
 
int main(void)
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n;
 
    cin >> n;
 
#if 1
    std::vector<size_type> answer;
    MyCompare comp;
 
    for (size_type i = 0; i < n; i++)
    {
        auto it = std::lower_bound(answer.begin(), answer.end(), i, comp);
        answer.emplace(it, i);
    }
 
    cout << '0';
    for (auto& a : answer)
        cout << ' ' << a + 1;
    cout << std::endl;
#else
    std::set<size_type, MyCompare> mp;
 
    for (size_type i = 0; i < n; i++)
        mp.emplace(i);
 
    cout << '0';
    for (auto& a : mp)
        cout << ' ' << a + 1;
    cout << std::endl;
#endif
 
    return 0;
}