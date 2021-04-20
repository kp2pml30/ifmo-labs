#include <cassert>
#include <array>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <iomanip>
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
#include <optional>
 
#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
1 10
2
 
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
// static auto cin = std::ifstream("matching.in");
// static auto cout = std::ofstream("matching.out");
#endif
 
using uint = std::uint32_t;
 
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
    MAKEOP(== ); MAKEOP(!= );
    MAKEOP(< ); MAKEOP(<= );
    MAKEOP(> ); MAKEOP(>= );
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
 
using Int = ModularT<std::int64_t, 1'000'000'007>;
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    int k, m;
 
    cin >> k >> m;
 
    auto tree = std::vector<Int>(m + 1);
    auto children = std::vector<Int>(m + 1);
    tree[0] = 1;
    children[0] = 1;
 
    auto c = std::vector<int>();
 
    for (int i = 0; i < k; i++)
    {
        int v;
        cin >> v;
        c.emplace_back(v);
    }
 
    std::sort(c.begin(), c.end());
 
    for (int i = 1; i <= m; i++)
    {
        for (auto const& c_i : c)
        {
            int add = i - c_i;
            if (add < 0)
                break;
            tree[i] += children[add];
        }
        for (int j = 0; j <= i; j++)
        {
            int add = i - j;
            //if (add < 0)
            //  break;
            children[i] += (Int)tree[j] * tree[add];
        }
    }
 
    for (int i = 1; i < tree.size(); i++)
        cout << tree[i] << ' ';
 
    cout << std::endl;
 
    return 0;
}