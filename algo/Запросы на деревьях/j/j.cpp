// no dont look

#pragma comment(linker, "/STACK:10485760")

#include <vector>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <fstream>
#include <functional>
#include <memory>
#include <set>
#include <map>

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
9
3 2
4 2
1 2
5 1
1 6
7 6
6 8
8 9
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
// auto cin = std::ifstream("minonpath.in");
// auto cout = std::ofstream("minonpath.out");
#endif

constexpr auto min_neutral = std::numeric_limits<std::int32_t>::max();

using uint = std::uint32_t; 

int main(void)
{
  std::size_t n, m;
  cin >> n;
  std::vector<std::size_t> answer(n + 1);
  std::vector<std::size_t> sizes(n + 1);

  std::vector<std::set<size_t>> graph(n + 1);
  for (std::size_t i = 2; i <= n; i++)
  {
    std::size_t u, v;
    cin >> u >> v;
    graph[u].insert(v);
    graph[v].insert(u);
  }


  std::function<void (std::size_t from, std::size_t to)> dfs_to_tree = [&](std::size_t from, std::size_t to) {
    for (const auto &a : graph[to])
      if (a != from)
        dfs_to_tree(to, a);
    sizes[to] = 1;
    for (const auto &a : graph[to])
      if (a != from)
        sizes[to] += sizes[a];
  };

  std::size_t current_n_div2 = 0;
  std::function<std::size_t (std::size_t from, std::size_t vert)> dfs_find_centroid = [&](std::size_t from, std::size_t vert) -> std::size_t {
    for (const auto &a : graph[vert])
      if (a != from && sizes[a] > current_n_div2)
        return dfs_find_centroid(vert, a);
    return vert;
  };

  dfs_to_tree(0, 1);

  current_n_div2 = n / 2;
  std::vector<std::size_t> current = {dfs_find_centroid(0, 1)}, following;
  // answerr is already 0

  while (!current.empty())
  {
    for (auto &processing : current)
    {
      // processing is a centroid
      dfs_to_tree(0, processing);
      for (auto &a : graph[processing])
      {
        graph[a].erase(processing);
        current_n_div2 = sizes[a] / 2;
        std::size_t centroid = dfs_find_centroid(processing, a);
        answer[centroid] = processing;
        following.push_back(centroid);
      }
    }
    current.swap(following);
    following.clear();
  }

  for (std::size_t i = 1; i <= n; i++)
    cout << answer[i] << ' ';
  cout << std::endl;
  return 0;
}