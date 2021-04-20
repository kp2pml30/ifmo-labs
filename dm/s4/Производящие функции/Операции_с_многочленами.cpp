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
1 3
1 2
1 4 5 2
 
 
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
 
    LazyArray(std::vector<type> vec, Func f)
        : f(std::move(f))
        , vec(std::move(vec))
    {}
};
 
template<typename T, typename Func>
LazyArray(std::vector<T>, Func)->LazyArray<T, Func>;
 
template<typename T>
auto factorial = LazyArray(
    std::vector<T>(1, {1}),
    [](std::vector<T>& vec) noexcept
    {
        vec.emplace_back(vec.back() * vec.size());
    });
 
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
    : val(std::move(t))
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
    MAKEOP(/)
    // MAKEOP(/)
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
    MAKEOP(==) MAKEOP(!= )
    MAKEOP(<) MAKEOP(<=)
    MAKEOP(>) MAKEOP(>=)
#undef MAKEOP
 
    friend std::ostream& operator<<(std::ostream& strm, Th const& a) noexcept
    {
        strm << a.val;
        return strm;
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
 
    class DivIterator
    {
    private:
        Polynom a, b, c;
        int index = 0;
    private:
        void calc()
        {
            type res;
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
        // no need to filter
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
 
using Int = ModularT<std::int64_t, 998'244'353>;
using Poly = Polynom<Int>;
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    int n, m;
    cin >> n >> m;
 
    Poly p, q;
    for (int i = 0; i <= n; i++)
    {
        int val;
        cin >> val;
        p[i] = val;
    }
    for (int i = 0; i <= m; i++)
    {
        int val;
        cin >> val;
        q[i] = val;
    }
 
    auto printSmart = [](Poly const& poly, int desiredDeg) {
        cout << desiredDeg << '\n' << poly;
        for (int i = poly.deg(); i < desiredDeg; i++)
            cout << " 0";
        cout << '\n';
    };
    auto printDflt = [](Poly const& poly) {
        auto deg = poly.deg();
        cout << deg << '\n' << poly << '\n';
    };
    printSmart(p + q, std::max(p.deg(), q.deg()));
    printDflt(p * q);
 
    {
        auto it = Poly::DivIterator(p, q);
        for (int i = 0; i < 1000; i++, ++it)
            cout << *it << ' ';
        cout << '\n';
    }
    cout << std::flush;
 
    return 0;
}