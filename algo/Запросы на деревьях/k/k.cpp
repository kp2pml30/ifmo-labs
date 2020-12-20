// no dont look

#pragma comment(linker, "/STACK:10485760")

#include <array>
#include <vector>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <fstream>
#include <functional>
#include <memory>
#include <set>
#include <map>
#include <cstdint>

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
10 10
1 2
2 3
3 4
2 5
2 6
3 7
3 8
3 9
3 10
3 9
4 8
7 6
7 8
7 9
9 8
9 2
3 4
7 5
4 4
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

using size_type = std::uint32_t;

int main(void)
{
  size_type n, m;
  cin >> n >> m;

  size_type log2n = 0;
  {
    size_type ndup = n;
    while (ndup >>= 1)
      log2n++;
    if (n > (1 << log2n))
      log2n++;
  }

  std::vector<size_type>
    upper_centroid(n + 1),
    sizes(n + 1);
  std::vector<std::int32_t> depth(n + 1), depth_of_subtree(n + 1);
  std::vector<std::vector<size_type>> min_at_dist(n + 1);

  std::vector<std::set<size_type>> graph(n + 1);
  for (size_type i = 2; i <= n; i++)
  {
    size_type u, v;
    cin >> u >> v;
    graph[u].insert(v);
    graph[v].insert(u);
  }

  // lca decl
  std::vector<std::vector<size_type>> dynamic(n + 1, std::vector<size_type>(log2n + 1, 0));
  auto lca = [&](size_type u, size_type v) -> size_type {
    if (u == v)
      return u;
    if (depth[u] > depth[v])
      std::swap(u, v);
    for (int i = log2n; i >= 0; i--)
      if (depth[dynamic[v][i]] - depth[u] >= 0)
        v = dynamic[v][i];
    if (u == v)
      return u == 0 ? 1 : u;
    for (int i = log2n; i >= 0; i--)
      if (dynamic[u][i] != dynamic[v][i])
      {
        u = dynamic[u][i];
        v = dynamic[v][i];
      }
    auto ans = dynamic[u][0];
    return ans == 0 ? 1 : ans;
  };
  auto get_dist = [&](size_type u, size_type v) {
    auto lc = lca(u, v);
    return depth[u] + depth[v] - depth[lc] * 2;
  };

  // depth + parents + lca dymaics
  {
    std::vector<size_type> dynamics_order;
    dynamics_order.reserve(n + 1);
    size_type depth_c = 1;
    std::function<void (size_type from, size_type to)> dfs_depth = [&](size_type from, size_type to) {
      dynamics_order.push_back(to);
      dynamic[to][0] = from;
      depth[to] = depth_c;
      depth_c++;
      
      for (const auto &a : graph[to])
        if (a != from)
          dfs_depth(to, a);
      depth_c--;
    };
    dfs_depth(0, 1);

    // dynamics
    for (size_type j = 1; j <= log2n; j++)
      for (const auto &i : dynamics_order)
        dynamic[i][j] = dynamic[dynamic[i][j - 1]][j - 1];
    dynamics_order.clear();
    dynamics_order.shrink_to_fit();
  }

  {
    std::function<void (size_type from, size_type to)> dfs_to_tree = [&](size_type from, size_type to) {
      sizes[to] = 1;
      std::int32_t subtree_d = 0;
      for (const auto &a : graph[to])
        if (a != from)
        {
          dfs_to_tree(to, a);
          sizes[to] += sizes[a];
          subtree_d = std::max(depth_of_subtree[a], subtree_d);
        }
      subtree_d++;
      depth_of_subtree[to] = subtree_d;
      return subtree_d;
    };
    dfs_to_tree(0, 1);

    size_type current_n_div2 = 0;
    std::function<size_type (size_type from, size_type vert)> dfs_find_centroid = [&](size_type from, size_type vert) -> size_type {
      for (const auto &a : graph[vert])
        if (a != from && sizes[a] > current_n_div2)
          return dfs_find_centroid(vert, a);
      return vert;
    };

    std::function<void (size_type vert)> dfs_build_centroid = [&](size_type vert) {
      {
        size_type cur = upper_centroid[vert];
        while (cur != 0)
        {
          size_type dist = get_dist(cur, vert);
          min_at_dist[cur][dist] = std::min(min_at_dist[cur][dist], vert);
          cur = upper_centroid[cur];
        }
      }
      dfs_to_tree(0, vert);
      min_at_dist[vert].resize(depth_of_subtree[vert], vert);
      for (auto &a : graph[vert])
      {
        graph[a].erase(vert);
        current_n_div2 = sizes[a] / 2;
        size_type centroid = dfs_find_centroid(vert, a);
        upper_centroid[centroid] = vert;
        dfs_build_centroid(centroid);
      }
    };
    current_n_div2 = n / 2;
    dfs_build_centroid(dfs_find_centroid(0, 1));
  }

  for (auto &b : min_at_dist)
    for (size_type i = 1; i < b.size(); i++)
      b[i] = std::min(b[i], b[i - 1]);

  for (size_type i = 0; i < m; i++)
  {
    size_type q, q0, d;
    cin >> q0 >> d;
    q = q0;
    size_type ans = q;
    while (q != 0)
    {
      size_type dist = get_dist(q0, q);
      if (dist <= d)
        ans = std::min(ans, min_at_dist[q][std::min((std::size_t)(d - dist), min_at_dist[q].size() - 1)]);
      q = upper_centroid[q];
    }
    cout << ans << '\n';
  }

  cout << std::flush;
  return 0;
}