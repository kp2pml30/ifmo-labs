#include <vector>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <fstream>
#include <functional>
#include <memory>

using size_type = std::uint32_t;

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
10
1 2
2 3
3 10
3 5
1 4
4 7
7 8
4 9
1 6
13
+ 5 8 2
+ 10 9 8
+ 6 6 -1
? 1
? 2
? 3
? 4
? 5
? 6
? 7
? 8
? 9
? 10
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
// auto cin = std::ifstream("minonpath.in");
// auto cout = std::ofstream("minonpath.out");
#endif

constexpr auto min_neutral = std::numeric_limits<std::int32_t>::max();

using BlankType = std::tuple<>;

template<typename KeyType>
static void FreePtr(KeyType *& ptr)
{
  if (ptr != nullptr)
  {
    delete ptr;
    ptr = nullptr;
  }
}

template<typename ValueType>
class ImplicitSplayTree
{
private:
public:
  class Node
  {
  public:
    ValueType data;
    std::int64_t key = 0; // it is not a key!

    struct
    {
      union
      {
        Node *upper;
        size_type index = 0;
      };
      bool isRoot = true;
    } upper_data;

    std::int64_t lazyProp = 0;

    Node
      *left = nullptr,
      *right = nullptr;

    Node(const ValueType data) : key(0), data(data) {}

    /*
    ~Node(void)
    {
      FreePtr(left);
      FreePtr(right);
    }
    */

    void Propagate(void)
    {
      key += lazyProp;
      if (left != nullptr) left->lazyProp += lazyProp;
      if (right != nullptr) right->lazyProp += lazyProp;
      lazyProp = 0;
    }

    Node * SetLeft(Node *left)
    {
      if (left != nullptr)
        left->upper_data.upper = this, left->upper_data.isRoot = false;
      this->left = left;
      UpdateKey();
      return left;
    }

    Node * SetRight(Node *right)
    {
      if (right != nullptr)
        right->upper_data.upper = this, right->upper_data.isRoot = false;
      this->right = right;
      UpdateKey();
      return right;
    }

    void Set(Node *left, Node *right)
    {
      SetLeft(left);
      SetRight(right);
    }

    void UpdateKey(void)
    {
      /*
      key = 1
        + (left == nullptr ? 0 : left->key)
        + (right == nullptr ? 0 : right->key)
        ;
        */
    }

    Node * Splay(void)
    {
      Propagate();
      while (!upper_data.isRoot)
      {
        // zig
        if (upper_data.upper->upper_data.isRoot)
        {
          upper_data.upper->Propagate();
          Propagate();

          if (upper_data.upper->left == this) // left zig
          {
            auto
              p = upper_data.upper,
              a = left,
              b = right,
              c = upper_data.upper->right;
            upper_data = upper_data.upper->upper_data;
            p->Set(b, c);
            Set(a, p);
          }
          else // right zig
          {
            auto
              p = upper_data.upper,
              a = p->left,
              b = left,
              c = right;
            upper_data = upper_data.upper->upper_data;
            p->Set(a, b);
            Set(p, c);
          }
          // zig is always last
          return this;
        } // end of zig

        upper_data.upper->upper_data.upper->Propagate();
        upper_data.upper->Propagate();
        Propagate();

        auto
          left1 = this == upper_data.upper->left,
          left2 = upper_data.upper == upper_data.upper->upper_data.upper->left;
        switch ((int)(left2 << 1) | (int)left1)
        {
        case 0: // r-r zig zig
        {
          auto
            p = upper_data.upper,
            g = p->upper_data.upper,
            a = g->left,
            b = p->left,
            c = left,
            d = right;
          if (!g->upper_data.isRoot)
            if (g->upper_data.upper->left == g)
              g->upper_data.upper->left = this;
            else
              g->upper_data.upper->right = this;
          upper_data = g->upper_data;

          g->Set(a, b);
          p->Set(g, c);
          Set(p, d);
        }
        break;
        case 1: // r-l zig zag
        {
          auto
            p = upper_data.upper,
            g = p->upper_data.upper,
            a = g->left,
            b = left,
            c = right,
            d = p->right;
          if (!g->upper_data.isRoot)
            if (g->upper_data.upper->left == g)
              g->upper_data.upper->left = this;
            else
              g->upper_data.upper->right = this;
          upper_data = g->upper_data;

          g->Set(a, b);
          p->Set(c, d);
          Set(g, p);
        }
        break;
        case 2: // l-r zig zag
        {
          auto
            p = upper_data.upper,
            g = p->upper_data.upper,
            a = p->left,
            b = left,
            c = right,
            d = g->right;
          if (!g->upper_data.isRoot)
            if (g->upper_data.upper->left == g)
              g->upper_data.upper->left = this;
            else
              g->upper_data.upper->right = this;
          upper_data = g->upper_data;

          p->Set(a, b);
          g->Set(c, d);
          Set(p, g);
        }
        break;
        case 3: // l-l zig zig
        {
          auto
            p = upper_data.upper,
            g = p->upper_data.upper,
            a = left,
            b = right,
            c = p->right,
            d = g->right;
          if (!g->upper_data.isRoot)
            if (g->upper_data.upper->left == g)
              g->upper_data.upper->left = this;
            else
              g->upper_data.upper->right = this;
          upper_data = g->upper_data;

          g->Set(c, d);
          p->Set(b, g);
          Set(a, p);
        }
        break;
        }
      }
      return this;
    } // end of 'splay'
  };
};

using NodeType = ImplicitSplayTree<size_type>::Node;

int main(void)
{
  std::ios_base::sync_with_stdio(false);
  cin.tie(nullptr);

  size_type n;
  cin >> n;

  std::vector<NodeType *> tree;
  std::vector<size_type> depth(n + 1);

  tree.reserve(n + 1);

  for (size_type i = 0; i <= n; i++)
    tree.push_back(new NodeType(i));

  {
    std::vector<std::vector<size_type>> graph(n + 1);
    for (size_type i = 1; i < n; i++)
    {
      size_type u, v;
      cin >> u >> v;
      graph[u].push_back(v);
      graph[v].push_back(u);
    }
    size_type depth_c = 0;
    std::function<void (size_type from, size_type to)> dfs_to_tree = [&](size_type from, size_type to) {
      depth_c++;
      depth[to] = depth_c;
      tree[to]->upper_data.index = from;
      for (const auto &a : graph[to])
        if (a != from)
          dfs_to_tree(to, a);
      depth_c--;
    };
    dfs_to_tree(0, 1);
  }

  auto expose = [&](NodeType *node) {
    while (true)
    {
      node->Splay();
      if (node->upper_data.index == 0)
        return;
      NodeType *n2 = tree[node->upper_data.index];
      n2->Splay();
      if (n2->left != nullptr)
      {
        n2->left->upper_data.isRoot = true;
        n2->left->upper_data.index = n2->data;
        n2->left = nullptr;
      }
      n2->SetLeft(node);
    }
  };

  size_type m;
  cin >> m;

  for (size_type i = 0; i < m; i++)
  {
    char c;
    cin >> c;
    if (c == '+')
    {
      size_type u, v;
      std::int64_t d;
      cin >> u >> v >> d;

      if (u == v)
      {
        tree[u]->key += d;
        continue;
      }
      if (depth[u] > depth[v])
        std::swap(u, v);

      auto
        treev = tree[v],
        treeu = tree[u];

      expose(treev);
      expose(treeu);
      treev->Splay();
      if (treev->upper_data.index == 0)
      {
        // u is an lca
        treev->key += d;
        treev->right->lazyProp += d;
        if (treeu->right != nullptr) treeu->right->lazyProp -= d;
      }
      else
      {
        auto lc = tree[treev->upper_data.index];
        lc->Splay();
        lc->key += d;
        if (lc->left != nullptr) lc->left->lazyProp += d;
        treeu->Splay();
        if (treeu->left != nullptr) treeu->left->lazyProp -= d;
        treev->key += d;
        if (treev->right != nullptr) treev->right->lazyProp += d;
      }
    }
    else if (c == '?')
    {
      size_type u;
      cin >> u;
      expose(tree[u]);
      cout << tree[u]->key << "\n";
    }
    else
      throw "wrong input";
  }

  cout << std::flush;
  return 0;
}