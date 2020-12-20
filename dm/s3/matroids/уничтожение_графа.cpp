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
6 7 10
1 2 3
1 3 3
2 3 3
3 4 1
4 5 5
5 6 4
4 6 5
)delim");
using std::cout;
#else
// using std::cin;
// using std::cout;
static auto cin = std::ifstream("destroy.in");
static auto cout = std::ofstream("destroy.out");
#endif
 
using uint = std::uint32_t;
using size_type = std::uint32_t;;
using weight_t = std::int64_t;
 
struct edge
{
    size_type a, b;
    weight_t w;
    size_type kek;
};
 
class DSU
{
public:
    std::vector<size_type> parent;
    DSU(size_type size) : parent(size)
    {
        for (size_type i = 0; i < size; i++)
            parent[i] = i;
    }
 
    size_type Parent(size_type v)
    {
        if (parent[v] == v)
            return v;
        return parent[v] = Parent(parent[v]);
    }
 
    void Join(size_type l, size_type r)
    {
        size_type
            L = Parent(l),
            R = Parent(r);
        parent[parent[L]] = R;
    }
};
 
template<typename T>
void Kruskal(size_type n, std::vector<edge>& edges, T callback)
{
    std::sort(edges.begin(), edges.end(), [](const auto &a, const auto &b) { return a.w > b.w; });
    DSU dsu(n + 1);
    for (const auto &e : edges)
    {
        if (dsu.Parent(e.a) != dsu.Parent(e.b))
        {
            dsu.Join(e.a, e.b);
            callback(e);
        }
    }
}
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n, m;
    weight_t s;
    cin >> n >> m >> s;
    std::vector<edge> edges(m);
 
    weight_t sumt = 0;
    for (size_type i = 0; i < m; i++)
    {
        size_type a, b;
        weight_t w;
        cin >> a >> b >> w;
        sumt += w;
        a--;
        b--;
        edges[i] = {a, b, w, i + 1};
    }
 
    std::unordered_set<size_type> taken;
 
    weight_t takent = 0;
 
    Kruskal(n, edges, [&](edge const& e) {
        takent += e.w;
        taken.emplace(e.kek);
    });
 
    for (size_type i = 0; i < m; i++)
    {
        if (sumt - takent <= s)
            break;
        if (taken.find(edges[i].kek) == taken.end())
        {
            taken.emplace(edges[i].kek);
            takent += edges[i].w;
        }
    }
 
    cout << m - taken.size() << std::endl;
    for (size_type i = 0; i < m; i++)
    {
        if (taken.find(edges[i].kek) == taken.end())
            cout << edges[i].kek << ' ';
    }
    cout << std::endl;
    return 0;
}