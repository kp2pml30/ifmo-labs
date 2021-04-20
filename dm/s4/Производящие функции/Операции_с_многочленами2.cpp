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
2 8
0 1 1
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
 
    void removeTail(int from) noexcept
    {
        vec.erase(vec.upper_bound(from), vec.end());
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
 
#if 1
using Int = ModularT<std::int64_t, 998'244'353>;
#else
using Int = float;
#endif
using Poly = Polynom<Int>;
 
template<typename T>
auto pow2(T const& a) { return a * a; }
 
template<typename F>
Poly makeSeries(int n, Poly const& p, F const& func)
{
    Poly ret;
    Poly mp;
    mp[0] = 1;
    for (int i = 0; i < n; i++)
    {
        Int coef = func(i);
         
        if (coef != 0)
            for (auto const& el : mp)
                ret[el.first] += coef * el.second;
        mp = mp * p;
        mp.removeTail(n);
        if (mp.empty())
            break;
    }
    return ret;
}
 
Poly makeSqrt(int n, Poly const& p)
{
    return makeSeries(n, p, [](int i) -> Int {
        if (i == 0)
            return 1;
        Int coef = factorial<Int>[2 * i] / ((2 * i - 1) * pow2(factorial<Int>[i]) * pow(Int(4), i));
        if (i % 2 == 0)
            coef *= -1;
        return coef;
    });
}
 
Poly makeExp(int n, Poly const& p)
{
    return makeSeries(n, p, [](int i) -> Int {
        return Int(1) / factorial<Int>[i];
    });
}
 
Poly makeLog(int n, Poly const& p)
{
    return makeSeries(n, p, [](int i) -> Int {
        if (i == 0)
            return 0;
        Int coef = Int(1) / i;
        if (i % 2 == 0)
            return coef * -1;
        return coef;
    });
}
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    int n, k;
    cin >> n >> k;
 
    Poly p;
    for (int i = 0; i <= n; i++)
    {
        int val;
        cin >> val;
        p[i] = val;
    }
    p.filter();
 
    auto printSmart = [](Poly&& poly, int desiredDeg) {
        poly.removeTail(desiredDeg);
        cout << poly;
        for (int i = poly.deg(); i < desiredDeg; i++)
            cout << " 0";
        cout << '\n';
    };
 
    printSmart(makeSqrt(k, p), k - 1);
    printSmart(makeExp(k, p), k - 1);
    printSmart(makeLog(k, p), k - 1);
 
    cout << std::flush;
 
    return 0;
}