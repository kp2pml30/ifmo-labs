// no dont look
 
#include <array>
#include <vector>
#include <iostream>
#include <algorithm>
#include <fstream>
#include <cstdint>
#include <cmath>
#include <sstream>
#include <map>
#include <functional>
#include <map>
#include <set>
#include <unordered_set>
#include <list>
#include <memory>
 
#if defined(_DEBUG)
auto cin = std::stringstream(R"delim(
6
  
1
10
011
0110
10011
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
#endif
 
using uint = std::uint32_t;
using size_type = std::uint32_t;
 
std::pair<size_type, size_type> MakePair(size_type a, size_type b)
{
    if (a < b)
        return {a, b};
    return {b, a};
}
 
template<typename T, typename Y>
bool operator<(std::pair<T, Y> const& l, std::pair<T, Y> const& r)
{
    return l.first < r.first
        || l.first == r.first && l.second < r.second;
}
 
#include <ctime>
 
bool FindInHam(std::vector<size_type> const& h, size_type u, size_type v)
{
    if (h.front() == u && h.back() == v
        || h.front() == v && h.back() == u)
        return true;
    for (size_type i = 0; i < h.size() - 1; i++)
        if (h[i] == u && h[i + 1] == v || h[i + 1] == u && h[i] == v)
            return true;
    return false;
}
 
void PrintGraph(std::vector<std::vector<bool>> const& g, std::vector<size_type> const& h)
{
    cout << "graph G" << clock() << " {\n";
    for (size_type i = 0; i < g.size(); i++)
        for (size_type j = i + 1; j < g.size(); j++)
            if (g[i][j])
            {
                cout << "_" << i << " -- _" << j;
                if (FindInHam(h, i, j))
                    cout << " [color=red]";
                cout << ";\n";
            }
    cout << "}\n";
}
 
int main(void)
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n;
 
    cin >> n;
 
#ifdef _DEBUG
#define _DEBUG1
#endif
 
#ifdef _DEBUG1
    std::vector<int> d = {2, 2, 4, 4, 5, 5};
    n = d.size();
#endif
 
    std::vector<std::vector<bool>> graph(n, std::vector<bool>(n, false));
    std::vector<size_type> deg(n, 0);
 
    {
        std::string str;
        std::getline(cin, str);
    }
 
    size_type ecount = 0;
 
#ifndef _DEBUG1
    for (size_type i = 0; i < n; i++)
    {
        std::string str;
        std::getline(cin, str);
        for (size_type j = 0; j < i; j++)
            if (str[j] == '1')
            {
                graph[i][j] = graph[j][i] = true;
                deg[i]++;
                deg[j]++;
                ecount++;
            }
    }
#else
    // censored
#endif
 
    std::vector<size_type> ham_path;
 
    std::function<void()> rec_chvatal = [&]() {
        if (ecount == n * (n - 1) / 2)
        {
            for (size_type i = 0; i < n; i++)
                ham_path.emplace_back(i);
            return;
        }
        size_type u = 0, v = 0;
        size_type mdeg = 0;
        for (size_type i = 0; i < n; i++)
        {
            // if (deg[i] == n - 1)
            //  continue;
            for (size_type j = i + 1; j < n; j++)
                if (deg[i] + deg[j] > mdeg && !graph[i][j])
                {
                    mdeg = deg[i] + deg[j];
                    u = i;
                    v = j;
                }
        }
        if (u == v)
            throw "up";
        ecount++;
        graph[u][v] = graph[v][u] = true;
        deg[u]++;
        deg[v]++;
        auto __recresetter = std::unique_ptr<void, std::function<void(void*)>>(
            (void*)1,
            [&, u, v](void*)
            {
                // revert
                ecount--;
                graph[u][v] = graph[v][u] = false;
                deg[u]--;
                deg[v]--;
            }
        );
        rec_chvatal();
 
#ifdef _DEBUG
        PrintGraph(graph, ham_path);
#endif
 
        if (ham_path.size() != n)
            throw "up";
 
        bool was = false;
 
        /*
            <-u --- v->
            <-v --- u->
        */
        if (ham_path.front() == u &&  ham_path.back() == v
                || ham_path.front() == v && ham_path.back() == u)
            was = true;
        else for (size_type i = 0; i < ham_path.size() - 1; i++)
        {
            auto j = i + 1;
            if (ham_path[i] == u && ham_path[j] == v || ham_path[i] == v && ham_path[j] == u)
            {
                /*
                   | rev |
                <- f --- i - j --- e ->
                             | rev |
                */
                std::reverse(ham_path.begin(), ham_path.begin() + i + 1);
                std::reverse(ham_path.begin() + j, ham_path.end());
                /*
                <- i --- f - e --- j ->
                */
                was = true;
                break;
            }
        }
        if (!was)
            return;
        if (u != ham_path.front() && u != ham_path.back()
                || v != ham_path.front() && v != ham_path.back())
            throw "up";
        u = ham_path.front();
        v = ham_path.back();
        for (size_type i = 1; i < ham_path.size() - 2; i++)
        {
            auto j = i + 1;
            auto hpi = ham_path[i];
            auto hpj = ham_path[j];
            /*
               _________
              |         |
            <-u --- i - j --- v->
                    |_________|
 
            delete <-u v->
            */
            if (graph[v][hpi] && graph[u][hpj])
            {
                std::reverse(ham_path.begin() + j, ham_path.end());
                /*
                <-u --- i - v --- j->
                */
                return;
            }
        }
        throw "up";
    };
 
    rec_chvatal();
#ifdef _DEBUG
    PrintGraph(graph, ham_path);
#endif
 
    for (auto const& a : ham_path)
        cout << a
#ifndef _DEBUG
        + 1 
#endif
        << ' ';
    std::cout << std::endl;
 
    return 0;
}