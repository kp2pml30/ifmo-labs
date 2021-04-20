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
3 30
1 2 3
4 5 6
 
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
    type operator*() const noexcept
    {
        return val;
    }
    friend Th operator+(Th const& a, Th const& b) noexcept
    {
        return a.val + b.val;
    }
    friend Th operator-(Th const& a, Th const& b) noexcept
    {
        return (a.val + MOD - b.val) % MOD;
    }
    Th& operator+=(Th const& r) noexcept
    {
        val += r.val;
        val %= MOD;
        return *this;
    }
    friend Th operator*(Th const& a, Th const& b) noexcept
    {
        return (std::int64_t)a.val * b.val % MOD;
    }
    Th& operator *= (Th const& r) noexcept
    {
        val = (std::int64_t)val * r.val % MOD;
        return *this;
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
};
 
template<typename T>
class Polynom
{
public:
    using type = T;
private:
    std::vector<type> vec;
public:
    Polynom() = default;
    Polynom(std::vector<type> v)
        : vec(std::move(v))
    {}
 
    type& operator[](int i) noexcept
    {
        if (vec.size() <= i)
            vec.resize(i + 1, type{});
        return vec[i];
    }
    type operator()(int i) const noexcept
    {
        if (i >= vec.size())
            return 0;
        return vec[i];
    }
 
    void nullify() noexcept
    {
        vec.clear();
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
        // while (!vec.empty() && vec.back() == 0)
        //  vec.pop_back();
    }
 
    std::int64_t deg() const noexcept
    {
        if (vec.empty())
            return 0;
        return vec.size() - 1;
    }
 
    friend Polynom operator*(Polynom const& a, Polynom const& b) noexcept
    {
        Polynom ret;
        for (int ia = 0; ia <= a.deg(); ia++)
            for (int ib = 0; ib <= b.deg(); ib++)
                ret[ia + ib] += a(ia) * b(ib);
        ret.filter();
        return ret;
    }
};
 
#if 1
using Int = ModularT<std::int32_t, 104'857'601>;
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
 
    int n;
    std::int64_t desired;
    cin >> n >> desired;
    desired--;
 
    Poly a;
 
    // read a
    for (int i = 0; i < n; i++)
    {
        int val;
        cin >> val;
        if (val != 0)
            a[i] = val;
    }
 
    // read q
    auto q = Poly({1});
    for (int i = 0; i < n; i++)
    {
        int val;
        cin >> val;
        if (val != 0)
            q[i + 1] = -val;
    }
 
    Poly newq, newa, q1;
 
    while (desired >= q.deg())
    {
        auto qdeg = q.deg();
        for (int i = qdeg; i < qdeg * 2; i++)
            for (int j = 1; j <= qdeg; j++)
                a[i] += -1 * q(j) * a(i - j);
 
        q1.nullify();
        for (int i = 0; i <= qdeg; i++)
            if (i % 2 == 0)
                q1[i] = q(i);
            else
                q1[i] = 0 - q(i);
 
        q = q * q1;
        for (int i = 0; i <= a.deg(); i++)
            if (i % 2 == desired % 2)
                newa[i / 2] = a[i];
        std::swap(a, newa);
        newa.nullify();
        for (int i = 0; i <= q.deg(); i++)
            newq[i / 2] += q[i];
        std::swap(q, newq);
        newq.nullify();
        desired /= 2;
    }
 
    cout << *a(desired) << std::endl;
    return 0;
}