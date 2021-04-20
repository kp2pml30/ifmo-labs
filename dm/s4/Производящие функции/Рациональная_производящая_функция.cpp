#include <cassert>
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
#include <deque>
#include <variant>
#include <numeric>
 
#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
5
1 1 2 3 5
1 1 0 0 1
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
// static auto cin = std::ifstream("matching.in");
// static auto cout = std::ofstream("matching.out");
#endif
 
using uint = std::uint32_t;
using size_type = std::int64_t;
 
template<typename T, typename Func>
class LazyArray
{
public:
    using type = T;
private:
    Func f;
    std::vector<type> vec;
public:
    type const& operator[](int i) noexcept
    {
        while (i >= vec.size())
            f(vec);
        return vec[i];
    }
 
    LazyArray(std::vector<type> v, Func f)
        : f(std::move(f))
        , vec(std::move(v))
    {}
 
    LazyArray() = delete;
};
 
template<typename T, typename Func>
LazyArray(std::vector<T>, Func)->LazyArray<T, Func>;
 
template<typename T>
static auto factorial = LazyArray(
    std::vector<T>(1, {T(1)}),
    [](std::vector<T>& vec) noexcept {
    if (vec.empty())
        vec.emplace_back(1);
    vec.emplace_back(vec.back() * vec.size());
});
 
template<typename Th>
Th pow(Th base, int exp)
{
    Th result = 1;
    for (;;)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        if (!exp)
            break;
        base *= base;
    }
 
    return result;
}
 
template<typename T, T MOD>
class ModularT
{
public:
    using type = T;
private:
    type val;
    using Th = ModularT;
public:
    ModularT(type t)
        : val((t + MOD) % MOD)
    {}
    ModularT()
        : ModularT(0)
    {}
#define MAKEOP(op) \
    friend Th operator op(Th const& a, Th const& b) noexcept \
    { \
        return Th((a.val op b.val) % MOD); \
    } \
    Th& operator op##= (Th const& r) noexcept \
    { \
        val op##= r.val; \
        val %= MOD; \
        return *this; \
    }
    MAKEOP(+)
        MAKEOP(*)
#undef MAKEOP
        friend Th operator-(Th const& a, Th const& b) noexcept
    {
        return Th((a.val - b.val + MOD) % MOD);
    }
#define MAKEOP(op) \
    friend bool operator op(Th const& a, Th const& b) noexcept \
    { \
        return a.val op b.val; \
    }
    MAKEOP(== ) MAKEOP(!= )
        MAKEOP(< ) MAKEOP(<= )
        MAKEOP(> ) MAKEOP(>= )
#undef MAKEOP
 
        friend std::ostream& operator<<(std::ostream& strm, Th const& a) noexcept
    {
        strm << a.val;
        return strm;
    }
 
    friend Th operator/(Th const& a, Th const& b) noexcept
    {
        auto bneg = pow(b, MOD - 2);
        assert(b * bneg == 1);
        return a * bneg;
    }
};
 
template<typename T>
class Polynom
{
public:
    using type = T;
private:
    std::map<int, type> vec;
public:
    Polynom() = default;
    Polynom(std::vector<type> const& v)
    {
        for (int i = 0; i < v.size(); i++)
            if (v[i] != 0)
                vec[i] = v[i];
    }
 
    type& operator[](int i) noexcept
    {
        return vec[i];
    }
    type operator()(int i) const noexcept
    {
        auto iter = vec.find(i);
        if (iter == vec.end())
            return 0;
        return iter->second;
    }
 
    auto begin()
    {
        return vec.begin();
    }
    auto end()
    {
        return vec.end();
    }
    auto begin() const
    {
        return vec.begin();
    }
    auto end() const
    {
        return vec.end();
    }
 
    void removeTail(int from, bool inclusive = false) noexcept
    {
        auto iter = inclusive ? vec.lower_bound(from) : vec.upper_bound(from);
        vec.erase(iter, vec.end());
    }
 
    bool empty() const noexcept
    {
        return vec.empty();
    }
 
    void filter() noexcept
    {
        // c++ 20 // std::erase_if(vec.begin(), vec.end(), [](auto const& b) { return b.second == 0; });
        for (auto iter = vec.begin(); iter != vec.end();)
            if (iter->second == 0)
                iter = vec.erase(iter);
            else
                ++iter;
    }
 
    void filter(int v)
    {
        auto it = vec.find(v);
        if (it->second == 0)
            vec.erase(it);
    }
 
    int deg() const noexcept
    {
        if (vec.empty())
            return 0;
        return std::prev(vec.end())->first;
    }
 
    Polynom derivative() const noexcept
    {
        Polynom ret;
        for (auto const& a : vec)
            if (a.first != 0)
                ret[a.first - 1] += a.first * a.second;
        return ret;
    }
 
    friend Polynom operator+(Polynom const& a, Polynom const& b) noexcept
    {
        Polynom ret;
        for (auto const& ina : a)
            ret[ina.first] = ina.second;
        for (auto const& inb : b)
            ret[inb.first] += inb.second;
        ret.filter();
        return ret;
    }
 
    friend Polynom operator-(Polynom const& a, Polynom const& b) noexcept
    {
        Polynom ret;
        for (auto const& ina : a)
            ret[ina.first] = ina.second;
        for (auto const& inb : b)
            ret[inb.first] -= inb.second;
        ret.filter();
        return ret;
    }
 
    friend Polynom operator%(Polynom const& p, int k) noexcept
    {
        Polynom r;
        for (auto const& a : p)
            r[a.first % k] += a.second;
        r.filter();
        return r;
    }
 
    friend Polynom operator*(Polynom const& a, Polynom const& b) noexcept
    {
        Polynom ret;
        for (auto const& ina : a)
            for (auto const& inb : b)
                ret[ina.first + inb.first] += ina.second * inb.second;
        ret.filter();
        return ret;
    }
 
    friend std::ostream& operator<<(std::ostream& s, Polynom const& r) noexcept
    {
        auto iter = r.begin();
        if (iter == r.end())
        {
            s << '0';
            return s;
        }
        int i = 0;
        while (iter != r.end())
        {
            while (i < iter->first)
            {
                if (i != 0)
                    s << ' ';
                s << '0';
                i++;
            }
            if (i != 0)
                s << ' ';
            s << iter->second;
            i++;
            ++iter;
        }
        return s;
    }
};
 
#if 0
using Int = ModularT<std::int64_t, 998'244'353>;
#else
using Int = std::int64_t;
// using Int = float;
#endif
using Poly = Polynom<Int>;
 
template<typename T>
auto pow2(T const& a) { return a * a; }
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    int k;
    cin >> k;
 
    Poly a;
    for (int i = 0; i < k; i++)
    {
        int val;
        cin >> val;
        if (val != 0)
            a[i] = val;
    }
 
    Poly q;
    q[0] = 1;
    for (int i = 0; i < k; i++)
    {
        int val;
        cin >> val;
        if (val != 0)
            q[i + 1] = -val;
    }
 
    q.filter();
 
    Poly p;
 
    for (int i = 0; i < k; i++)
    {
        Int got = 0;
        for (int j = 1; j <= i; j++)
            got += a(i - j) * q(j);
        p[i] = a(i) + got;
    }
 
    p.filter();
 
    cout
        << p.deg() << '\n' << p << '\n'
        << q.deg() << '\n' << q << '\n'
        << std::flush
        ;
 
    return 0;
}