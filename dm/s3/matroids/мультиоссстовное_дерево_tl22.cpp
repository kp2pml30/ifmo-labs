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
3 4
1 2
2 3
3 1
3 2

)delim");
using std::cout;
#else
// using std::cin;
// using std::cout;
static auto cin = std::ifstream("multispan.in");
static auto cout = std::ofstream("multispan.out");
#endif
 
using uint = std::uint32_t;
using size_type = std::uint32_t;
 
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
 
template<typename F1, typename F2, typename F3, typename F4>
void intersectMatroids(AnswerHandler& answer, F1 const& takeMe, F2 const& removeMe, F3 const& oracle1, F4 const& oracle2)
{
    // rip
RESTART:
    while (true)
    {
        std::unordered_map<size_type, std::vector<size_type>> intersectionEdges;
 
        std::vector<size_type> fromSet;
        std::unordered_set<size_type> toSet;
 
        for (auto const& not_cur : answer.not_answer)
        {
            bool both = false;
            if (oracle1(not_cur))
            {
                fromSet.emplace_back(not_cur);
                both = true;
            }
            if (oracle2(not_cur))
            {
                toSet.emplace(not_cur);
                if (both)
                {
                    takeMe(not_cur);
                    answer.Add(not_cur);
                    goto RESTART;
                }
            }
        }
 
        if (fromSet.empty() || toSet.empty())
            return;
 
        for (auto const& cur : answer.answer)
        {
            removeMe(cur);
 
            for (auto const& not_cur : answer.not_answer)
            {
                if (oracle1(not_cur))
                    intersectionEdges[cur].emplace_back(not_cur);
                if (oracle2(not_cur))
                    intersectionEdges[not_cur].emplace_back(cur);
            }
 
            takeMe(cur);
        }
 
        // bfs
        std::unordered_map<size_type, size_type> bfs_backs;
        auto bfs_thisone = std::move(fromSet);
        decltype(bfs_thisone) bfs_nextone;
        for (auto const& a : bfs_thisone)
            bfs_backs[a] = a;
 
        size_type path_end = -1;
        while (!bfs_thisone.empty())
        {
            for (auto const& vert : bfs_thisone)
                for (auto const& to : intersectionEdges[vert])
                {
                    if (bfs_backs.count(to) != 0)
                        continue;
                    bfs_backs[to] = vert;
                    if (toSet.count(to) != 0)
                    {
                        path_end = to;
                        goto BFS_DONE;
                    }
                    if (!intersectionEdges[to].empty())
                        bfs_nextone.emplace_back(to);
                }
            std::swap(bfs_thisone, bfs_nextone);
            bfs_nextone.clear();
        }
    BFS_DONE:
        // we are done with this
        if (path_end == (size_type)-1)
            return;
        // remove edges
        {
            auto copy = path_end;
            copy = bfs_backs[copy];
            while (copy != bfs_backs[copy])
            {
                removeMe(copy);
                answer.Rem(copy);
                copy = bfs_backs[copy];
                copy = bfs_backs[copy];
            }
        }
        // add edges
        {
            auto copy = path_end;
            while (copy != bfs_backs[copy])
            {
                takeMe(copy);
                answer.Add(copy);
                copy = bfs_backs[copy];
                copy = bfs_backs[copy];
            }
            takeMe(copy);
            answer.Add(copy);
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
 
int main()
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    // std::cout << "HELLO" << std::endl;
 
    size_type n, m;
    cin >> n >> m;
 
    struct edge
    {
        size_type a, b;
        std::uint16_t col;
        size_type ind;
    };
 
    auto edges_base = std::vector<edge>(m);
 
    for (auto const& i : Range(m))
    {
        size_type a, b;
        std::uint16_t color = i + 1;
        cin >> a >> b;
        a--;
        b--;
        edges_base[i] = {a, b, color, i};
    }
 
    auto edges = edges_base;
 
    std::bitset<2048> current_colors;
    std::vector<std::set<size_type>> current_graph(n);
    std::vector<size_type> vert_different_markers(n);
    std::iota(vert_different_markers.begin(), vert_different_markers.end(), 0);
    size_type next_marker = n;
 
    auto oracle1 = [&](size_type i) {
        edge const& e = edges[i];
        return !current_colors[e.col];
    };
 
    auto oracle2 = [&](size_type i) {
        edge const& e = edges[i];
        return vert_different_markers[e.a] != vert_different_markers[e.b];
    };
 
    std::function<void(size_type cur, std::uint64_t mrk, size_type from)> paintWithMarks = [&](size_type cur, size_type mrk, size_type from) {
        vert_different_markers[cur] = mrk;
        for (auto const& v : current_graph[cur])
            if (v != from)
                paintWithMarks(v, mrk, cur);
    };
 
    auto takeMe = [&](size_type i) {
        edge const& e = edges[i];
        current_colors[e.col] = true;
        paintWithMarks(e.b, vert_different_markers[e.a], e.b);
        current_graph[e.a].emplace(e.b);
        current_graph[e.b].emplace(e.a);
    };
 
    auto removeMe = [&](size_type i) {
        edge const& e = edges[i];
        current_colors[e.col] = false;
        current_graph[e.a].erase(e.b);
        current_graph[e.b].erase(e.a);
        paintWithMarks(e.b, next_marker++, e.b);
    };
 
    auto answer = AnswerHandler(m);
    answer.answer.reserve(m * n);
    answer.not_answer.reserve(m * n);
 
    // std::cout << "PREKRUSK" << std::endl;
 
    // find initial set
    {
        std::vector<size_type> eb(m);
        std::iota(eb.begin(), eb.end(), 0);
        Kruskal(n, eb,
            [&](size_type i) { return std::pair(edges[i].a, edges[i].b); },
            [&](size_type i) { takeMe(i); answer.Add(i); }
        );
    }
     
    std::unordered_set<size_type> answer_copy;
    size_type iteration = 0;
 
    // std::cout << "KRUSK" << std::endl;
 
    while (answer.answer.size() % (n - 1) == 0)
    {
        iteration++;
        if (iteration >= 18)
            break;
        // std::cout << iteration << std::endl;
        answer_copy = answer.answer;
 
        vert_different_markers.reserve(n);
        for (auto const& a : Range(n))
            vert_different_markers.emplace_back(next_marker++);
        current_graph.resize(current_graph.size() + n);
        for (auto const& a : Range(m))
        {
            answer.not_answer.emplace(edges.size());
            // edges_base[i] = {a, b, color, i};
            edges.push_back({
                    edges[a].a + n * iteration,
                    edges[a].b + n * iteration,
                    edges[a].col,
                    (size_type)edges.size()
                });
        }
 
        intersectMatroids(answer, takeMe, removeMe, oracle1, oracle2);
 
        if (answer_copy.size() == answer.answer.size())
            break;
    }
 
    // std::cout << "DONE" << std::endl;
 
    std::vector<std::vector<size_type>> trueAnswer(answer_copy.size() / (n - 1));
    for (auto const& e : answer_copy)
        trueAnswer[edges[e].ind / m].emplace_back(edges[e].col);
 
    cout << trueAnswer.size() << '\n';
    for (auto const& v : trueAnswer)
    {
        for (auto const& b : v)
            cout << b << ' ';
        cout << '\n';
    }
    return 0;
}