#include <vector>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <fstream>
#include <functional>
#include <memory>

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
5 10
link 2 5
link 1 5
size 1
cut 2 5
size 1
size 2
link 2 3
link 2 4
link 3 5
size 1
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
    std::int64_t key; // size of subtree
    std::int64_t additional = 0;
    ValueType data; // index in the forest
    bool needsReverse = false;

    Node
      *left = nullptr,
      *right = nullptr;

    struct
    {
      union
      {
        Node *upper;
        std::size_t index = 0;
      };
      bool isRoot = true;
    } upper_data;

    Node(const ValueType data) : key(1), data(data) {}

    void Propagate(void)
    {
      if (needsReverse)
      {
        needsReverse = false;
        std::swap(left, right);
        if (left  != nullptr) left ->needsReverse ^= 1;
        if (right != nullptr) right->needsReverse ^= 1;
      }
    }

    void PropagateUppers(void)
    {
      if (!upper_data.isRoot)
        upper_data.upper->PropagateUppers();
      Propagate();
    }

    Node * SetLeft(Node *left)
    {
      if (left != nullptr)
        left->upper_data.upper = this, left->upper_data.isRoot = false;
      this->left = left;
      return left;
    }

    Node * SetRight(Node *right)
    {
      if (right != nullptr)
        right->upper_data.upper = this, right->upper_data.isRoot = false;
      this->right = right;
      return right;
    }

    void Set(Node *left, Node *right)
    {
      SetLeft(left);
      SetRight(right);
      UpdateKey();
    }

    void UpdateKey(void)
    {
      key = 1
        + additional
        + (left  == nullptr ? 0 : left ->key)
        + (right == nullptr ? 0 : right->key)
        ;
    }

    Node * Splay(void)
    {
      PropagateUppers();
      while (!upper_data.isRoot)
      {
        // zig
        if (upper_data.upper->upper_data.isRoot)
        {
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
              c = right,
              r = right;
            upper_data = upper_data.upper->upper_data;
            p->Set(a, b);
            Set(p, c);
          }
          // zig is always last
          return this;
        } // end of zig
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

using NodeType = ImplicitSplayTree<std::size_t>::Node;

int main(void)
{
  std::size_t n, m;
  cin >> n >> m;

  std::vector<NodeType *> tree;
  for (std::size_t i = 0; i <= n; i++)
    tree.push_back(new NodeType(i));

  std::vector<std::size_t> parent(n + 3);

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

        n2->additional += n2->left->key;
        n2->left = nullptr;
      }
      n2->additional -= node->key;
      n2->SetLeft(node);
      n2->UpdateKey();
    }
  };

  auto makeRoot = [&expose](NodeType *node) {
    expose(node);
    if (!node->upper_data.isRoot)
      throw "up";
    if (node->right != nullptr)
    {
      node->right->needsReverse ^= 1;
      node->right->upper_data.isRoot = true;
      node->right->upper_data.index = node->data;
      // doesn't change a key
      node->additional += node->right->key;
      node->right = nullptr;
    }
  };

  for (std::size_t i = 0; i < m; i++)
  {
    std::string c;
    cin >> c;
    if (c == "link")
    {
      std::size_t u, v;
      cin >> u >> v;

      // link v to u
      expose(tree[u]);
      makeRoot(tree[v]);
      tree[v]->upper_data.index = u;
      tree[u]->additional += tree[v]->key;
      tree[u]->UpdateKey();
      // expose(tree[u].get());
    }
    else if (c == "cut")
    {
      std::size_t u, v;
      cin >> u >> v;
      makeRoot(tree[u]);
      expose(tree[v]);
      if (tree[v]->right != tree[u])
        throw "up";
      tree[v]->right->upper_data.isRoot = true;
      tree[v]->right->upper_data.index = 0;
      tree[v]->right = nullptr;
      tree[v]->UpdateKey();
    }
    else if (c == "size")
    {
      std::size_t u;
      cin >> u;
      // if (u == v)
      //   cout << "1\n";
      // else
      /*
      {
        auto getRoot = [&expose](auto cur) {
          expose(cur);
          cur->Splay();
          cur->Propagate();
          while (cur->right != nullptr)
          {
            cur = cur->right;
            cur->Propagate();
          }
          cur->Splay();
          return cur;
        };
        if (getRoot(tree[u].get()) == getRoot(tree[v].get()))
          cout << "1\n";
        else
          cout << "0\n";
      }
      */
      // makeRoot(tree[u]);
      expose(tree[u]);
      cout << tree[u]->key << '\n';
    }
    else
      throw "wrong input";
  }

  cout << std::flush;
  return 0;
}