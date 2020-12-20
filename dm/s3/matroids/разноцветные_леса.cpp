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
#include <bitset>
 
#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
9 12
1 2 1
2 3 2
3 4 3
4 5 4
5 6 1
6 7 2
7 8 3
8 9 4
1 3 5
1 4 6
1 5 7
1 6 8

)delim");
using std::cout;
#else
// using std::cin;
// using std::cout;
static auto cin = std::ifstream("rainbow.in");
static auto cout = std::ofstream("rainbow.out");
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
 
template<typename T> Range(T)->Range<T>;
template<typename T> Range(T, T)->Range<T>;
template<typename T> Range(T, T, T)->Range<T>;
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n, m;
    cin >> n >> m;
 
    struct edge
    {
        size_type a, b;
        std::uint8_t col;
        size_type ind;
    };
 
    std::vector<edge> edges(m);
 
    for (auto const& i : Range(m))
    {
        size_type a, b;
        std::uint16_t color;
        cin >> a >> b >> color;
        a--;
        b--;
        if (color > 110)
            throw "up";
        edges[i] = {a, b, std::uint8_t(color - 1), i};
    }
 
    std::bitset<128> current_colors;
    std::vector<std::set<size_type>> current_graph(n);
    std::vector<size_type> vert_different_markers(n);
    std::iota(vert_different_markers.begin(), vert_different_markers.end(), 0);
    std::uint64_t next_marker = n;
 
    auto isIndepColor = [&](edge const& e) {
        return !current_colors[e.col];
    };
 
    auto isIndepTree = [&](edge const& e) {
        return vert_different_markers[e.a] != vert_different_markers[e.b];
    };
 
    std::function<void(size_type cur, std::uint64_t mrk, size_type from)> paintWithMarks = [&](size_type cur, std::uint64_t mrk, size_type from) {
        // we now that it is a tree
        vert_different_markers[cur] = mrk;
        for (auto const& v : current_graph[cur])
            if (v != from)
                paintWithMarks(v, mrk, cur);
    };
 
    auto justEmplaceEdge = [&](edge e) {
        current_colors[e.col] = true;
        current_graph[e.a].emplace(e.b);
        current_graph[e.b].emplace(e.a);
    };
 
    auto takeEdge = [&](edge e) {
        current_colors[e.col] = true;
        paintWithMarks(e.b, vert_different_markers[e.a], e.b);
        current_graph[e.a].emplace(e.b);
        current_graph[e.b].emplace(e.a);
    };
 
    auto removeEdge = [&](edge e) {
        current_colors[e.col] = false;
        current_graph[e.a].erase(e.b);
        current_graph[e.b].erase(e.a);
        paintWithMarks(e.b, next_marker++, e.b);
    };
 
    std::unordered_set<size_type> answer;
    std::unordered_set<size_type> not_answer;
    for (auto const& i : Range(m))
        not_answer.emplace(i);
 
    auto add2Answer = [&](size_type ind) {
        if (answer.count(ind) != 0)
            throw "up";
        answer.emplace(ind);
        not_answer.erase(ind);
    };
 
    auto remFromAnswer = [&](size_type ind) {
        if (answer.count(ind) == 0)
            throw "up";
        answer.erase(ind);
        not_answer.emplace(ind);
    };
 
    auto xorFromAnswer = [&](size_type ind) {
        if (answer.count(ind) != 0)
            remFromAnswer(ind);
        else
            add2Answer(ind);
    };
 
    // find initial set
    for (auto const& e : edges)
        if (isIndepColor(e) && isIndepTree(e))
        {
            takeEdge(e);
            add2Answer(e.ind);
            continue;
        }
    // rip
RESTART:
    while (true)
    {
        std::unordered_map<size_type, std::vector<size_type>> intersectionEdges;
 
        std::vector<size_type> fromSet; // color
        std::unordered_set<size_type> toSet; // jungle
 
        for (auto const& not_cur : not_answer)
        {
            bool both = false;
            if (isIndepColor(edges[not_cur]))
            {
                fromSet.emplace_back(not_cur);
                both = true;
            }
            if (isIndepTree(edges[not_cur]))
            {
                toSet.emplace(not_cur);
                if (both)
                {
                    takeEdge(edges[not_cur]);
                    add2Answer(not_cur);
                    goto RESTART;
                }
            }
        }
 
        if (fromSet.empty() || toSet.empty())
            goto ANSWER;
 
        for (auto const& cur : answer)
        {
            auto old_vert_different_markers = vert_different_markers;
            removeEdge(edges[cur]);
 
            for (auto const& not_cur : not_answer)
            {
                // todo check arrows direcction
                if (isIndepColor(edges[not_cur]))
                    intersectionEdges[cur].emplace_back(not_cur);
                if (isIndepTree(edges[not_cur]))
                    intersectionEdges[not_cur].emplace_back(cur);
            }
 
            takeEdge(edges[cur]);
            justEmplaceEdge(edges[cur]);
        }
 
        // bfs
        std::vector<int> bfs_backs(m, -1);
        auto bfs_thisone = std::move(fromSet);
        decltype(bfs_thisone) bfs_nextone;
        for (auto const& a : bfs_thisone)
            bfs_backs[a] = (int)a;
 
        size_type path_end = -1;
        while (!bfs_thisone.empty())
        {
            for (auto const& vert : bfs_thisone)
                for (auto const& to : intersectionEdges[vert])
                {
                    if (bfs_backs[to] != -1)
                        continue;
                    bfs_backs[to] = vert;
                    if (toSet.count(to) != 0)
                    {
                        path_end = to;
                        goto BFS_DONE;
                    }
                    bfs_nextone.emplace_back(to);
                }
            std::swap(bfs_thisone, bfs_nextone);
            bfs_nextone.clear();
        }
    BFS_DONE:
        // we are done with this
        if (path_end == (size_type)-1)
            goto ANSWER;
        // remove edges
        {
            auto copy = path_end;
            copy = bfs_backs[copy];
            while (copy != bfs_backs[copy])
            {
                removeEdge(edges[copy]);
                remFromAnswer(copy);
                copy = bfs_backs[copy];
                copy = bfs_backs[copy];
            }
        }
        // add edges
        {
            auto copy = path_end;
            while (copy != bfs_backs[copy])
            {
                takeEdge(edges[copy]);
                add2Answer(copy);
                copy = bfs_backs[copy];
                copy = bfs_backs[copy];
            }
            takeEdge(edges[copy]);
            add2Answer(copy);
        }
    }
 
ANSWER:
    cout << answer.size() << '\n';
#ifdef _DEBUG
    std::vector<size_type> sorted(answer.begin(), answer.end());
    std::sort(sorted.begin(), sorted.end());
    for (auto const& e : sorted)
#else
    for (auto const& e : answer)
#endif
        cout
        << e
#if 1//defined(_DEBUG)
        + 1
#endif
        << ' ';
    cout << '\n';
    return 0;
}