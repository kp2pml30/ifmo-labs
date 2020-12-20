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
3 1
10 20 20
3 1 3 2
)delim");
using std::cout;
#else
// using std::cin;
// using std::cout;
static auto cin = std::ifstream("cycles.in");
static auto cout = std::ofstream("cycles.out");
#endif
 
using uint = std::uint32_t;
using size_type = std::uint64_t;;
using weight_t = std::int64_t;
 
template<typename T>
class Range
{
private:
    T b, e, s;
public:
    struct iterator
    {
        T b, s;
 
        T operator*() const noexcept { return b; }
        bool operator!=(iterator const& r) const noexcept
        {
            return b < r.b;
        }
 
        iterator& operator++() noexcept
        {
            b += s;
            return *this;
        }
        iterator operator++(int) noexcept
        {
            auto old = *this;
            b += s;
            return old;
        }
    };
    Range(T const& b, T const& e, T const& s)
    : b(b)
    , e(e)
    , s(s)
    {}
 
    Range(T const& b, T const& e)
    : Range(b, e, 1)
    {}
 
    Range(T const& e)
    : Range(0, e)
    {}
 
    iterator begin() const noexcept { return {b, s}; }
    iterator end() const noexcept { return {e, s}; }
};
 
template<typename T> Range(T)       -> Range<T>;
template<typename T> Range(T, T)    -> Range<T>;
template<typename T> Range(T, T, T) -> Range<T>;
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n, m;
    cin >> n >> m;
     
    std::vector<size_type> weight(n);
 
    std::multimap<size_type, size_type, std::greater<>> w2i;
 
    for (auto const& i : Range(n))
    {
        cin >> weight[i];
        w2i.emplace(weight[i], i);
    }
 
    std::vector<std::uint64_t> cycles(m);
 
    for (auto const& i : Range(m))
    {
        size_type cnt;
        cin >> cnt;
        std::uint64_t res = 0;
        for (auto const& _ : Range(cnt))
        {
            size_type c;
            cin >> c;
            c--;
            cycles[i] |= 1 << c;
        }
    }
 
    auto isIndep = [&](std::uint64_t check) {
        for (auto const& a : cycles)
            if ((a & check) == a)
                return false;
        return true;
    };
 
    std::uint64_t taken = 0;
    std::uint64_t taken_weight = 0;
    for (auto const& a : w2i)
    {
        auto brr = 1 << a.second;
        if (isIndep(taken | brr))
        {
            taken |= brr;
            taken_weight += a.first;
        }
    }
 
    cout << taken_weight << std::endl;
    return 0;
}