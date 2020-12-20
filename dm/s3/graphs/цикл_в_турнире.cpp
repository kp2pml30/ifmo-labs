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
 
#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
4
 
1
01
001
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
#endif
 
using uint = std::uint32_t;
using size_type = std::uint32_t;
 
int main(void)
{
    std::ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
 
    size_type n;
 
    cin >> n;
 
    std::vector<std::vector<bool>> graph(n, std::vector<bool>(n, false));
 
    {
        std::string str;
        std::getline(cin, str);
    }
 
    for (size_type i = 0; i < n; i++)
    {
        std::string str;
        std::getline(cin, str);
        for (size_type j = 0; j < i; j++)
            if (str[j] == '1')
                graph[i][j] = true;
            else
                graph[j][i] = true;
    }
 
    std::list<size_type> ham_path;
 
    {
        auto comp = [&](size_type l, size_type r) {
            return graph[l][r];
        };
        std::set<size_type, decltype(comp)> sorted(comp);
        for (size_type i = 0; i < n; i++)
            sorted.emplace(i);
        for (auto const& a : sorted)
            ham_path.emplace_back(a);
    }
 
    while (true)
    {
        auto i_0 = ham_path.end();
        for (auto b = ham_path.begin(); b != ham_path.end(); ++b)
            if (graph[ham_path.back()][*b])
            {
                i_0 = b;
                break;
            }
        if (i_0 == ham_path.end())
            throw "up";
        if (i_0 == ham_path.begin())
            break;
        bool done = false;
        auto i_m1 = std::prev(i_0);
        auto i_p1 = std::next(i_0);
        for (auto br = i_0; br != ham_path.end(); ++br)
        {
            auto nxt = std::next(br);
            if (nxt == ham_path.end())
                break;
            if (graph[*br][*i_m1] && graph[*i_m1][*nxt])
            {
                ham_path.splice(nxt, ham_path, i_m1);
                ham_path.splice(i_0, ham_path, std::prev(ham_path.end()));
                done = true;
                break;
            }
        }
        // i_m1 dominates everyone in vi..vn (if not done ofc)
        auto checked = i_m1;
        while (!done)
        {
            if (checked == ham_path.begin())
                throw "up";
            --checked;
            for (auto t = std::next(i_0); t != ham_path.end(); ++t)
                if (graph[*t][*checked])
                {
                    ham_path.splice(i_0, ham_path, std::next(t), ham_path.end());
                    done = true;
                    break;
                }
        }
    }
 
    for (auto const& a : ham_path)
        cout << a
#ifndef _DEBUG
        + 1
#endif
        << ' ';
    std::cout << std::endl;
 
    return 0;
}