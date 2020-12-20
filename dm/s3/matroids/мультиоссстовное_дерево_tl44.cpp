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
5 13
1 2
2 3
3 4
4 5
2 4
2 2
1 4
1 5
4 3
5 3
1 2
1 5
2 1
)delim");
using std::cout;
#else
// using std::cin;
// using std::cout;
static auto cin = std::ifstream("multispan.in");
static auto cout = std::ofstream("multispan.out");
#endif
 
using uint = std::uint32_t;
using size_type = std::uint16_t;
 
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
template<typename T> Range(int, T)->Range<T>;
template<typename T> Range(T, T)->Range<T>;
template<typename T> Range(T, T, T)->Range<T>;
template<typename T> Range(int, T, int)->Range<T>;
 
struct AnswerHandler
{
    std::unordered_set<size_type> answer;
    std::unordered_set<size_type> not_answer;
 
    AnswerHandler() = default;
 
    AnswerHandler(size_type n)
    {
        if (n == 0)
            return;
        while (n > 0)
            not_answer.emplace(--n);
        not_answer.emplace(0);
    }
 
    void Add(size_type a)
    {
        answer.emplace(a);
        not_answer.erase(a);
    }
 
    void Rem(size_type a)
    {
        answer.erase(a);
        not_answer.emplace(a);
    }
 
    std::size_t Size() const noexcept
    {
        return answer.size() + not_answer.size();
    }
};
 
struct Marked
{
    using T = size_type;
    std::unordered_set<T> marked;
    std::unordered_set<T> wasnt;
    std::vector<T> used;
 
    void Use(T t)
    {
        if (used[t] == 0)
            wasnt.erase(t);
        else if (used[t] == 1)
            marked.emplace(t);
        used[t]++;
    }
 
    void Unuse(T t)
    {
        if (used[t] == 2)
            marked.erase(t);
        else if (used[t] == 1)
            wasnt.emplace(t);
        used[t]--;
    }
};
 
template<typename F1, typename F2, typename F3>
void intersectMatroids(size_type N, Marked& marked, std::vector<AnswerHandler>& bases, F1 const& takeMe, F2 const& removeMe, F3 const& oracle)
{
    while (true)
    {
        // bfs
        std::unordered_map<size_type, std::pair<size_type, size_type>> bfs_backs;
        std::vector<size_type> bfs_thisone;
        for (auto const& a : marked.marked)
            bfs_thisone.emplace_back(a);
        decltype(bfs_thisone) bfs_nextone;
        for (auto const& a : bfs_thisone)
            bfs_backs[a] = {a, -1};
 
        size_type path_end = -1;
        while (!bfs_thisone.empty())
        {
            for (auto const& vert : bfs_thisone)
            {
                for (size_type m = 0; m < bases.size(); m++)
                    if (auto const& cur = vert; bases[m].answer.count(cur) != 0)
                    {
                        removeMe(m, cur);
 
                        auto taker = std::unique_ptr<size_type, std::function<void(size_type*)>>(&m, 
                            [&](size_type*) {
                            takeMe(m, cur);
                            });
 
                        for (auto const& not_cur : bases[m].not_answer)
                            if (oracle(m, not_cur))
                            {
                                auto to = std::pair(not_cur, m);
                                // G[cur].emplace(not_cur, m);
                                if (bfs_backs.count(to.first) == 0)
                                {
                                    bfs_backs[to.first] = {vert, to.second};
                                    if (marked.wasnt.count(to.first) != 0)
                                    {
                                        path_end = to.first;
                                        goto BFS_DONE;
                                    }
                                    bfs_nextone.emplace_back(to.first);
                                }
                            }
                    }
            }
            std::swap(bfs_thisone, bfs_nextone);
            bfs_nextone.clear();
        }
        // we are done with this, nothing found
        return;
BFS_DONE:
        auto prev = bfs_backs[path_end];
        while (prev.first != path_end)
        {
            removeMe(prev.second, prev.first);
            bases[prev.second].Rem(prev.first);
            takeMe(prev.second, path_end);
            bases[prev.second].Add(path_end);
            path_end = prev.first;
        }
    }
}
 
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
 
template<typename T, typename Y>
void Kruskal(size_type n, std::vector<size_type>& edges, Y const& getter, T const& callback)
{
    DSU dsu(n + 1);
    size_type repl = 0;
    for (const auto &e : edges)
    {
        auto[a, b] = getter(e);
        if (dsu.Parent(a) != dsu.Parent(b))
        {
            dsu.Join(a, b);
            callback(e);
        }
        else
            edges[repl++] = e;
    }
    edges.resize(repl);
}
 
#include <chrono>
 
int main()
{
    auto start = std::chrono::system_clock::now();
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n, m;
    cin >> n >> m;
 
    struct edge
    {
        size_type a, b;
        size_type ind;
    };
 
    auto edges_base = std::vector<edge>(m);
 
    for (auto const& i : Range(m))
    {
        size_type a, b;
        cin >> a >> b;
        a--;
        b--;
        edges_base[i] = {a, b, i};
    }
 
    auto edges = edges_base;
 
    std::vector<std::vector<std::set<size_type>>> current_graph(1);
    current_graph[0] = std::vector<std::set<size_type>>(n);
    std::vector<std::vector<std::uint32_t>> vert_different_markers(1);
    vert_different_markers[0] = std::vector<std::uint32_t>(n);
    std::iota(vert_different_markers[0].begin(), vert_different_markers[0].end(), 0);
    std::uint32_t next_marker = n;
 
    Marked marked;
    marked.used.resize(m, 0);
    for (auto const& a : Range(m))
        marked.wasnt.emplace(a);
 
    auto oracle = [&](size_type m, size_type i) {
        edge const& e = edges[i];
        return vert_different_markers[m][e.a] != vert_different_markers[m][e.b];
    };
 
    std::function<void(size_type, size_type, std::uint32_t, size_type)> paintWithMarks = [&](size_type m, size_type cur, std::uint32_t mrk, size_type from) {
        vert_different_markers[m][cur] = mrk;
        for (auto const& v : current_graph[m][cur])
            if (v != from)
                paintWithMarks(m, v, mrk, cur);
    };
 
    auto takeMe = [&](size_type m, size_type i) {
        edge const& e = edges[i];
        marked.Use(i);
        paintWithMarks(m, e.b, vert_different_markers[m][e.a], e.b);
        current_graph[m][e.a].emplace(e.b);
        current_graph[m][e.b].emplace(e.a);
    };
 
    auto removeMe = [&](size_type m, size_type i) {
        edge const& e = edges[i];
        marked.Unuse(i);
        current_graph[m][e.a].erase(e.b);
        current_graph[m][e.b].erase(e.a);
        paintWithMarks(m, e.b, next_marker++, e.b);
    };
 
    std::vector<AnswerHandler> answer(1);
    answer[0] = AnswerHandler(m);
    // find initial set
    {
        std::vector<size_type> eb(m);
        std::iota(eb.begin(), eb.end(), 0);
        Kruskal(n, eb,
            [&](size_type i) { return std::pair(edges[i].a, edges[i].b); },
            [&](size_type i) { takeMe(0, i); answer[0].Add(i); }
        );
    }
 
    std::vector<AnswerHandler> answer_copy;
 
    while (true)
    {
        // std::cout << answer.size() << std::endl;
        answer_copy = answer;
 
        answer.push_back(answer.back());
        current_graph.push_back(current_graph.back());
        vert_different_markers.push_back(vert_different_markers.back());
 
        for (auto& a : answer.back().answer)
            marked.Use(a);
 
        intersectMatroids(m, marked, answer, takeMe, removeMe, oracle);
 
        if (marked.marked.size() != 0)
            break;
    }
 
    cout << answer_copy.size() << '\n';
    for (auto const& t : answer_copy)
    {
        for (auto const& v : t.answer)
            cout << v + 1 << ' ';
        cout << '\n';
    }
#ifdef KAPRAL
    std::cout << std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now() - start).count() << std::endl;
#endif
    return 0;
}