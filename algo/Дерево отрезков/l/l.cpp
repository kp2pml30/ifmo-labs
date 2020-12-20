#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdio>
#include <fstream>

using uint = unsigned;

#if !defined(__OPTIMIZE__)
#	include <sstream>
auto cin = std::stringstream(R"delim(
2
2 1 1 1 1 1 1
1 0 0 0 1
1 0 1 0 3
2 0 0 0 0 0 0
2 0 0 0 0 1 0
1 0 1 0 -2
2 0 0 0 1 1 1
3
)delim");
#else
using std::cin;
// std::ifstream cin("crypto.in");
#endif

/*
 * descr class :
 *	type    - typename
 *	oper    - functional class
 *	neutral - static/non-static var of type
 */

namespace std
{
  template<>
  class vector<void> { public: vector(uint a) {} };
}

template<bool cond, typename iftrue, typename iffalse>
class selector
{
public:
  using type = iftrue;
};

template<typename iftrue, typename iffalse>
class selector<false, iftrue, iffalse>
{
public:
  using type = iffalse;
};

uint n;

class Container
{
public:
  int count = 0;
};

Container operator+(Container l, Container r)
{
  return Container({l.count + r.count});
}

template<uint dims>
class Tree
{
public:
  std::vector<Tree<dims - 1>> els;

  Tree(void) : els(2 * n - 1)
  {
  }

  template<typename ...Uint>
  void Add(Container value, uint x, uint lx, uint rx, uint first, Uint ...tail)
  {
    static_assert(sizeof...(tail) == dims - 1, "waaa");
    els[x].Add(value, 0, 0, n, tail...);
    if (rx - lx <= 1)
      return;
    uint m = (lx + rx) / 2;
    if (first < m)
      Add(value, 2 * x + 1, lx, m, first, tail...);
    else
      Add(value, 2 * x + 2, m, rx, first, tail...);
  }

  template<typename ...Uint>
  Container Sum(uint x, uint lx, uint rx, uint l, uint r, Uint ...tail)
  {
    if (l >= rx || lx >= r)
      return Container({0});
    if (lx >= l && rx <= r)
    {
      return els[x].Sum(0, 0, n, tail...);
    }
    uint m = (lx + rx) / 2;
    return Sum(2 * x + 1, lx, m, l, r, tail...) + Sum(2 * x + 2, m, rx, l, r, tail...);
  }
};

template<>
class Tree<1>
{
public:
  std::vector<Container> els;

  Tree(void) : els(2 * n - 1)
  {
  }

  void Add(Container value, uint x, uint lx, uint rx, uint first)
  {
    if (rx - lx <= 1)
    {
      els[x] = els[x] + value;
      return;
    }
    uint m = (lx + rx) / 2;
    if (first < m)
      Add(value, 2 * x + 1, lx, m, first);
    else
      Add(value, 2 * x + 2, m, rx, first);
    els[x] = els[2 * x + 1] + els[2 * x + 2];
  }

  Container Sum(uint x, uint lx, uint rx, uint l, uint r)
  {
    if (l >= rx || lx >= r)
      return Container({0});
    if (lx >= l && rx <= r)
      return els[x];
    uint m = (lx + rx) / 2;
    return Sum(2 * x + 1, lx, m, l, r) + Sum(2 * x + 2, m, rx, l, r);
  }
};

template<>
class Tree<0>;

int main(void)
{
  cin >> n;
  n--;
  n |= n >> 1;
  n |= n >> 2;
  n |= n >> 4;
  n |= n >> 8;
  n |= n >> 16;
  n++;
  Tree<3> tree;
  while (true)
  {
    int ty;
    cin >> ty;
    if (ty == 1)
    {
      int o;
      uint x, y, z;
      cin >> x >> y >> z >> o;
      tree.Add(Container({o}), 0, 0, n, x, y, z);
    }
    else if (ty == 2)
    {
      uint x1, y1, z1, x2, y2, z2;
      cin >> x1 >> y1 >> z1 >> x2 >> y2 >> z2;
      x2++;
      y2++;
      z2++;
      std::cout << tree.Sum(0, 0, n, x1, x2, y1, y2, z1, z2).count << std::endl;
    }
    else
      break;
  }
  return 0;
}
