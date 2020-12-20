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
7
1 2
2 3
2 4
5 2
5 6
7 5
3
1 7
2 4
7 6
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

template<typename Descr>
class MassTree
{
private:
  using type = typename Descr::type;
  Descr descr;
  std::vector<type> els, set;
  uint n;
  class Setter
  {
  private:
    MassTree *parent;
    uint index0, index1;
  public:
    Setter(MassTree *parent, uint index0, uint index1) : parent(parent), index0(index0), index1(index1) {}
    void operator=(const type &r)
    {
      return parent->setf(index0, index1, r, 0, 0, parent->n);
    }
  };
  void propagate(uint x, uint lx, uint rx)
  {
    if (set[x] == descr.setneutral)
      return;
    els[x] = set[x];
    if (rx - lx == 1)
      return;
    set[2 * x + 1] = set[x];
    set[2 * x + 2] = set[x];
    set[x] = descr.setneutral;
  }
  void setf(uint l, uint r, const type &v, uint x, uint lx, uint rx)
  {
    propagate(x, lx, rx);
    if (l >= rx || lx >= r)
      return;
    if (lx >= l && rx <= r)
    {
      set[x] = v;
      els[x] = v;
      return;
    }
    auto m = (lx + rx) / 2;
    setf(l, r, v, 2 * x + 1, lx, m);
    setf(l, r, v, 2 * x + 2, m, rx);
  }
  type calc(uint w, uint x, uint lx, uint rx)
  {
    if (set[x] != descr.setneutral)
      return set[x];
    propagate(x, lx, rx);
    if (rx - lx == 1)
      return els[x];
    auto m = (lx + rx) / 2;
    if (w < m)
      return calc(w, 2 * x + 1, lx, m);
    else
      return calc(w, 2 * x + 2, m, rx);
  }
public:
  MassTree(int inp)
  {
    n = inp;
    n--;
    n |= n >> 1;
    n |= n >> 2;
    n |= n >> 4;
    n |= n >> 8;
    n |= n >> 16;
    n++;
    set.resize(2 * n - 1, descr.setneutral);
    els.resize(2 * n - 1, 1);
  }
  Setter operator[](std::pair<uint, uint> i) { return Setter(this, i.first, i.second); }

  type operator()(uint w)
  {
    return calc(w, 0, 0, n);
  }
};

class setter
{
public:
  long long val;
  setter(void) : val(1LL << 63) {}
  setter(long long val) : val(val) {}
  bool operator<(const setter &r) const { return val < r.val; }
  setter & operator=(const setter &r) { val = r.val; return *this; }
  bool operator==(const setter &r) { return val == r.val; }
  bool operator!=(const setter &r) { return val != r.val; }
  setter operator+(const setter &r) const { return setter(val + r.val); }
};

class SetOper
{
public:
  setter operator()(setter l, setter r)
  {
    if (l == (1LL << 63))
      return r;
    return l;
  }
};

class mindescr
{
public:
  using type = setter;
  SetOper setoper;
  const type setneutral = 1LL << 63;
};

int main(void)
{
  std::size_t n, m;
  cin >> n;

  std::size_t log2n = 0;
  {
    std::size_t ndup = n;
    while (ndup >>= 1)
      log2n++;
    if (n > (1 << log2n))
      log2n++;
  }

  std::vector<std::vector<std::size_t>> dynamic(n + 1, std::vector<std::size_t>(log2n + 1, 0));
  std::vector<std::int32_t> depth(n + 1);

  std::vector<std::vector<size_t>> tree(n + 1);
  std::vector<size_t> jumps_order;
  jumps_order.reserve(n + 5);

  {
    std::vector<std::vector<size_t>> graph(n + 1);
    for (std::size_t i = 2; i <= n; i++)
    {
      std::size_t u, v;
      cin >> u >> v;
      graph[u].push_back(v);
      graph[v].push_back(u);
    }
    std::size_t depth_c = 1;
    std::function<void (std::size_t from, std::size_t to)> dfs_to_tree = [&](std::size_t from, std::size_t to) {
      jumps_order.push_back(to);
      depth[to] = depth_c;
      tree[from].push_back(to);
      dynamic[to][0] = from;
      depth_c++;
      for (const auto &a : graph[to])
        if (a != from)
          dfs_to_tree(to, a);
      depth_c--;
    };
    dfs_to_tree(0, 1);
  }

  // jumps
  for (std::size_t j = 1; j <= log2n; j++)
    for (const auto &i : jumps_order)
    // for (std::size_t i = 1; i <= n; i++)
      dynamic[i][j] = dynamic[dynamic[i][j - 1]][j - 1];


  // lca
  auto lca = [&](std::size_t u, std::size_t v) -> std::size_t {
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

  cin >> m;
  std::set<std::size_t> path_starts;
  std::map<std::size_t, std::size_t> path_ends; // contains the least lca it is connected with

  for (std::size_t i = 0; i < m; i++)
  {
    std::size_t u, v;
    cin >> u >> v;
    if (u == v)
      continue;
    if (u > v)
      std::swap(u, v);
    auto lc = lca(u, v);
    if (lc == u)
    {
      // one path :  u--v
      path_starts.insert(u);
      auto prev = path_ends[v];
      if (prev == 0)
        path_ends[v] = u;
      else
        path_ends[v] = (depth[prev] <= depth[u] ? prev : u);
    }
    else
    {
      // two paths : u--lca--v
      path_starts.insert(lc);
      auto prev = path_ends[v];
      if (prev == 0)
        path_ends[v] = lc;
      else
        path_ends[v] = (depth[prev] <= depth[lc] ? prev : lc);

      prev = path_ends[u];
      if (prev == 0)
        path_ends[u] = lc;
      else
        path_ends[u] = (depth[prev] <= depth[lc] ? prev : lc);
    }
  }

#ifdef _DEBUG
  std::vector<std::size_t> vertsqueue;
#endif
  std::size_t current_depth = -1;
  std::map<std::size_t, std::size_t> found_uppers; // {upper_vert => it's index}

  MassTree<mindescr> range_tree(n);
  // std::vector<bool> colors(n + 5, 1);

  // colors[0] = 0;
  range_tree[std::make_pair(0, 1)] = 0;

  std::size_t ANSWER = 0;
  std::function<void(std::size_t where)> dfs = [&](std::size_t where) {
#ifdef _DEBUG
    vertsqueue.push_back(where);
#endif
    current_depth++;
    auto end_iter = path_ends.find(where);
    if (end_iter != path_ends.cend())
    {
      auto start = found_uppers.find(end_iter->second);
      if (start != found_uppers.cend())
        // throw "up";
      range_tree[std::make_pair(start->second + 1, current_depth + 1)] = 0;
      // for (std::size_t i = start->second + 1; i < current_depth + 1; i++)
      //   colors[i] = false;
    }
    if (path_starts.count(where))
      found_uppers[where] = current_depth;
    for (const auto &e : tree[where])
      dfs(e);

    // ANSWER += colors[current_depth];
    ANSWER += range_tree(current_depth).val;

    range_tree[std::make_pair(current_depth, current_depth + 1)] = 1;
    // colors[current_depth] = true;
#ifdef _DEBUG
    vertsqueue.pop_back();
#endif
    current_depth--;
    found_uppers.erase(where);
  };

  dfs(1);

  cout << ANSWER << std::flush;
  return 0;
}