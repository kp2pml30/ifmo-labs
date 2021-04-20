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
auto cin = std::stringstream(R"delim(S(L(B))
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
    std::map<int, type> vec;
public:
    Polynom() = default;
    Polynom(std::initializer_list<type> const& v)
    {
        int i = 0;
        for (auto const& a : v)
        {
            if (a != 0)
                vec[i] = a;
            i++;
        }
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
 
    type eval(type wh) const noexcept
    {
        type res = 0;
        for (auto const& a : vec)
            res += pow(wh, a.first) * a.second;
        return res;
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
 
    void nullify() noexcept
    {
        vec.clear();
    }
 
    int deg() const noexcept
    {
        if (vec.empty())
            return 0;
        return std::prev(vec.end())->first;
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
            for (auto const& j : c)
                res += j.second * b(index - j.first);
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
 
    Polynom& operator+=(Polynom const& b) noexcept
    {
        for (auto const& inb : b)
            vec[inb.first] += inb.second;
        filter();
        return *this;
    }
 
    Polynom& operator-=(Polynom const& b) noexcept
    {
        for (auto const& inb : b)
            vec[inb.first] -= inb.second;
        filter();
        return *this;
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
 
    friend Polynom operator*(Polynom const& a, type const& b) noexcept
    {
        if (b == 0)
            return {};
        Polynom ret;
        for (auto const& ina : a)
            ret[ina.first] += ina.second * b;
        return ret;
    }
 
    Polynom& operator*=(type const& b) noexcept
    {
        if (b == 0)
        {
            nullify();
            return *this;
        }
        for (auto& a : vec)
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
        for (auto& a : vec)
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
 
    friend std::ostream& operator<<(std::ostream& s, Polynom const& r) noexcept
    {
        auto iter = r.begin();
        if (iter == r.end())
        {
            s << type();
            return s;
        }
        int i = 0;
        while (iter != r.end())
        {
            while (i < iter->first)
            {
                if (i != 0)
                    s << ' ';
                s << type();
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
using Int = std::uint64_t;
#endif
using Rat = Ratio<Int>;
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
 
Int chooseRat(Int f, Int c)
{
    if (f == 0)
        return c == 0;
    auto res = Rat(1, factorial<Int>[c]);
    for (int i = 0; i < c; i++)
        res *= (f - i);
    if (res.d != 1)
        throw "up";
    return res.n;
}
 
void Fetch(std::istream& s, char c)
{
    if (s.get() != c)
        throw "up";
}
 
Poly parseB();
Poly parseL();
Poly parseS();
Poly parseP();
 
Poly parse()
{
    auto c = cin.get();
    if (c == 'B')
        return parseB();
    if (c == 'L')
        return parseL();
    if (c == 'S')
        return parseS();
    if (c == 'P')
        return parseP();
    throw "bad";
}
 
Poly parseB()
{
    return Poly{0, 1};
}
 
Poly parseP()
{
    Fetch(cin, '(');
    auto a = parse();
    Fetch(cin, ',');
    auto b = parse();
    Fetch(cin, ')');
    auto res = a * b;
    res.removeTail(7);
    return res;
}
 
Poly parseL()
{
    Fetch(cin, '(');
    auto p = parse();
    Fetch(cin, ')');
    p[0] = 0;
    p.filter(0);
    Poly ret;
#if 1
    ret[0] = 1;
    for (int n = 1; n <= 6; n++)
        for (int i = 1; i <= n; i++)
            ret[n] += p(i) * ret(n - i);
    ret.filter();
#else
    Poly::DivIterator iter(Poly{1}, Poly{1} - p);
    for (int i = 0; i < 7; i++)
    {
        ret[i] = *iter;
        ++iter;
    }
#endif
    return ret;
}
 
class PolyClamp : public Poly
{
public:
    using Poly::Poly;
 
    PolyClamp& operator*=(PolyClamp const& r)
    {
        (Poly&)*this *= (Poly const&)r;
        removeTail(7);
        return *this;
    }
};
 
Poly parseS()
{
    Fetch(cin, '(');
    auto p = parse();
    Fetch(cin, ')');
 
    p[0] = 0;
 
    std::vector<std::vector<Int>> m;
 
    m.emplace_back(6, 1);
    for (int n = 1; n <= 6; n++)
    {
        m.emplace_back(7);
        m[n][0] = 0;
        for (int k = 1; k <= 6; k++)
        {
            Int res = 0;
            for (int i = 0; i <= n / k; i++)
                res += chooseRat(p(k) + i - 1, i) * m[n - i * k][k - 1];
            m[n][k] = res;
        }
    }
 
    Poly ret;
    for (int n = 0; n <= 6; n++)
        if (m[n][n] != 0)
            ret[n] = m[n][n];
 
    return ret;
}
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    auto res = parse();
 
    for (int i = 0; i <= 6; i++)
        cout << res(i) << ' ';
 
    cout << std::flush;
 
    return 0;
}