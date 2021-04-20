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
7 6
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
 
template<typename T>
auto pow2(T const& a) { return a * a; }
 
template<typename Th>
Th pow(Th base, int exp)
{
    Th result = {1};
    while (true)
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
 
// numeric types
 
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
    MAKEOP(+);
    MAKEOP(*);
#undef MAKEOP
    friend Th operator-(Th const& a, Th const& b) noexcept
    {
        return Th((a.val - b.val + MOD) % MOD);
    }
    Th& operator-=(Th const& a) noexcept
    {
        *this = *this - a;
        return *this;
    }
#define MAKEOP(op) \
    friend bool operator op(Th const& a, Th const& b) noexcept \
    { \
        return a.val op b.val; \
    }
    MAKEOP(==); MAKEOP(!=);
    MAKEOP(<); MAKEOP(<=);
    MAKEOP(>); MAKEOP(>=);
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
class Ratio
{
public:
    using type = T;
    type n, d;
    Ratio(T i = 0)
        : n(std::move(i))
        , d(1)
    {}
 
    Ratio(T no, T de)
        : n(std::move(no))
        , d(std::move(de))
    {
        filter();
    }
 
    void filter() noexcept
    {
        auto gcd = std::gcd(n, d);
        n /= gcd;
        d /= gcd;
    }
 
    Ratio inv() const noexcept
    {
        assert(n != 0);
        if (n >= 0)
            return Ratio(d, n);
        return Ratio(-d, -n);
    }
 
    friend Ratio operator+(Ratio const& a, Ratio const& b) noexcept
    {
        Ratio ret;
        if (a.d == b.d)
        {
            ret.n = a.n + b.n;
            ret.d = a.d;
        }
        else
        {
            auto g = std::gcd(a.d, b.d);
            ret.n = a.n * (b.d / g) + b.n * (a.d / g);
            ret.d = (a.d / g) * b.d;
        }
        ret.filter();
        return ret;
    }
    friend Ratio operator*(Ratio const& a, Ratio const& b) noexcept
    {
        auto gan_bd = std::gcd(a.n, b.d);
        auto gad_bn = std::gcd(a.d, b.n);
 
        return Ratio((a.n / gan_bd) * (b.n / gad_bn), (a.d / gad_bn) * (b.d / gan_bd));
    }
    Ratio operator-() const noexcept
    {
        return Ratio(-n, d);
    }
    Ratio& operator*=(Ratio const& r) noexcept
    {
        *this = *this * r;
        return *this;
    }
    Ratio& operator+=(Ratio const& r) noexcept
    {
        *this = *this + r;
        return *this;
    }
    friend Ratio operator/(Ratio const& a, Ratio const& b) noexcept
    {
        return a * b.inv();
    }
 
    friend std::ostream& operator<<(std::ostream& s, Ratio const& r) noexcept
    {
        if (r.d < 0)
            throw "up";
        auto copy = r;
        copy.filter();
        s << copy.n << '/' << copy.d;
        return s;
    }
 
    friend bool operator==(Ratio const& a, Ratio const& b)
    {
        return a.n == b.n && a.d == b.d;
    }
    friend bool operator<(Ratio const& a, Ratio const& b)
    {
        return a.n * b.d < b.n * a.d;
    }
    friend bool operator<=(Ratio const& a, Ratio const& b)
    {
        return a.n * b.d <= b.n * a.d;
    }
    friend bool operator!=(Ratio const& a, Ratio const& b)
    {
        return !(a == b);
    }
    friend bool operator>(Ratio const& a, Ratio const& b)
    {
        return b < a;
    }
    friend bool operator>=(Ratio const& a, Ratio const& b)
    {
        return b <= a;
    }
};
 
// sparse polynom
template<typename T>
class Polynom
{
public:
    using type = T;
private:
    std::deque<type> vec;
public:
    Polynom() = default;
    Polynom(std::initializer_list<type> const& v)
    {
        int i = 0;
        for (auto const& a : v)
        {
            if (a != 0)
                operator[](i) = a;
            i++;
        }
    }
 
    void MulT() noexcept
    {
        vec.push_front(0);
    }
 
    type& operator[](int i) noexcept
    {
        if (i >= vec.size())
            vec.resize(i + 1);
        return vec[i];
    }
    type operator()(int i) const noexcept
    {
        if (i >= vec.size())
            return 0;
        return vec[i];
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
 
    bool empty() const noexcept
    {
        return vec.empty();
    }
 
    void filter() noexcept
    {
    }
 
    void filter(int v)
    {
    }
 
    void nullify() noexcept
    {
        vec.clear();
    }
 
    class DivIterator
    {
    private:
        Polynom a, b, c;
        int index = 0;
    private:
        void calc()
        {
            type res{};
            int inc = 0;
            for (auto const& j : c)
            {
                res += j * b(index - inc);
                inc++;
            }
            res = (a(index) - res) / b(0);
            c[index] = res;
            c.filter(index);
        }
    public:
        DivIterator(Polynom a, Polynom b)
            : a(std::move(a))
            , b(std::move(b))
        {
            if (this->b(0) == 0)
                throw "up";
            calc();
        }
        type operator*() const noexcept
        {
            return c(index);
        }
        void operator++() noexcept
        {
            index++;
            calc();
        }
    };
 
    Polynom& operator+=(Polynom const& b) noexcept
    {
        int inbi = 0;
        for (auto const& inb : b)
        {
            vec[inbi] += inb.second;
            inbi++;
        }
        filter();
        return *this;
    }
 
    friend Polynom operator+(Polynom const& a, Polynom const& b) noexcept
    {
        Polynom ret = a;
        ret += b;
        return ret;
    }
 
    Polynom& operator-=(Polynom const& b) noexcept
    {
        int inbi = 0;
        for (auto const& inb : b)
        {
            operator[](inbi) -= inb;
            inbi++;
        }
        filter();
        return *this;
    }
 
    friend Polynom operator-(Polynom const& a, Polynom const& b) noexcept
    {
        Polynom ret = a;
        ret -= b;
        return ret;
    }
 
    friend Polynom operator*(Polynom const& a, Polynom const& b) noexcept
    {
        Polynom ret;
        int inai = 0;
        for (auto const& ina : a)
        {
            int inbi = 0;
            for (auto const& inb : b)
            {
                ret[inai + inbi] += ina * inb;
                inbi++;
            }
            inai++;
        }
        ret.filter();
        return ret;
    }
 
    friend Polynom operator*(Polynom const& a, type const& b) noexcept
    {
        if (b == 0)
            return {};
        Polynom ret;
        int inai = 0;
        for (auto const& ina : a)
        {
            ret[inai] += ina.second * b;
            inai++;
        }
        return ret;
    }
 
    Polynom& operator*=(type const& b) noexcept
    {
        if (b == 0)
        {
            nullify();
            return *this;
        }
        for (auto& a : *this)
            a.second *= b;
        return *this;
    }
 
    Polynom& operator*(type const& b) noexcept
    {
        if (b == 0)
        {
            nullify();
            return *this;
        }
        for (auto& a : *this)
            a.second *= b;
        return *this;
    }
 
    friend Polynom operator*(type const& b, Polynom const& a) noexcept
    {
        return a * b;
    }
 
    friend Polynom& operator*=(Polynom& a, Polynom const& b) noexcept
    {
        auto d = a * b;
        a = d;
        return a;
    }
};
 
#if 1
using Int = ModularT<std::int64_t, 998'244'353>;
#else
using Int = std::uint64_t;
#endif
using Rat = Ratio<std::int64_t>;
using Poly = Polynom<Int>;
 
template<typename T>
T choose(int f, int c)
{
    if (f == 0)
        return c == 0;
    T res{1};
    for (int i = 0; i < c; i++)
        res *= (f - i);
    return res / factorial<T>[c];
}
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    int k, n;
    cin >> k >> n;
 
    Poly p{0, 1}, q{1};
 
    for (int i = 3; i <= k; i++)
    {
        auto pold = std::move(p);
        p = q;
        p.MulT();
        q -= pold;
    }
 
    Poly::DivIterator iter(p, q);
 
    ++iter;
 
    for (int i = 1; i <= n; i++)
    {
        cout << *iter << '\n';
        ++iter;
    }
 
    cout << std::flush;
 
    return 0;
}