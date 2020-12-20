#define _CRT_SECURE_NO_WARNINGS

#include <cstdio>
#include <utility>
#include <tuple>

#include <algorithm>

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
    Node
      *upper = nullptr,
      *left = nullptr,
      *right = nullptr;
    std::size_t key;
    ValueType data;

    Node(const ValueType data) : key(1), data(data) {}

    ~Node(void)
    {
      FreePtr(left);
      FreePtr(right);
    }

    Node * SetLeft(Node *left)
    {
      if (left != nullptr)
        left->upper = this;
      this->left = left;
      return left;
    }

    Node * SetRight(Node *right)
    {
      if (right != nullptr)
        right->upper = this;
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
        + (left  == nullptr ? 0 : left ->key)
        + (right == nullptr ? 0 : right->key)
        ;
    }

    std::size_t LeftEq(std::size_t accum = 0)
    {
      return accum + 1 + (left == nullptr ? 0 : left->key);
    }

    /*
    void UpdateUppers(void)
    {
      UpdateKey();
      auto up = upper;
      while (up != nullptr)
      {
        up->UpdateKey();
        up = up->upper;
      }
    }
    */

    Node * Splay(void)
    {
      // already upper
      if (upper == nullptr)
        return this;
      do
      {
        // zig
        if (upper->upper == nullptr)
        {
          if (upper->left == this) // left zig
          {
            auto
              p = upper,
              a = left,
              b = right,
              c = upper->right;
            upper = upper->upper;
            p->Set(b, c);
            Set(a, p);
          }
          else // right zig
          {
            auto
              p = upper,
              a = p->left,
              b = left,
              c = right,
              r = right;
            upper = upper->upper;
            p->Set(a, b);
            Set(p, c);
          }
          // zig is always last
          return this;
        } // end of zig
        auto
          left1 = this == upper->left,
          left2 = upper == upper->upper->left;
        switch ((int)(left2 << 1) | (int)left1)
        {
        case 0: // r-r zig zig
        {
          auto
            p = upper,
            g = p->upper,
            a = g->left,
            b = p->left,
            c = left,
            d = right;
          if (g->upper != nullptr)
            if (g->upper->left == g)
              g->upper->left = this;
            else
              g->upper->right = this;
          upper = g->upper;

          g->Set(a, b);
          p->Set(g, c);
          Set(p, d);
        }
        break;
        case 1: // r-l zig zag
        {
          auto
            p = upper,
            g = p->upper,
            a = g->left,
            b = left,
            c = right,
            d = p->right;
          if (g->upper != nullptr)
            if (g->upper->left == g)
              g->upper->left = this;
            else
              g->upper->right = this;
          upper = g->upper;

          g->Set(a, b);
          p->Set(c, d);
          Set(g, p);
        }
        break;
        case 2: // l-r zig zag
        {
          auto
            p = upper,
            g = p->upper,
            a = p->left,
            b = left,
            c = right,
            d = g->right;
          if (g->upper != nullptr)
            if (g->upper->left == g)
              g->upper->left = this;
            else
              g->upper->right = this;
          upper = g->upper;

          p->Set(a, b);
          g->Set(c, d);
          Set(p, g);
        }
        break;
        case 3: // l-l zig zig
        {
          auto
            p = upper,
            g = p->upper,
            a = left,
            b = right,
            c = p->right,
            d = g->right;
          if (g->upper != nullptr)
            if (g->upper->left == g)
              g->upper->left = this;
            else
              g->upper->right = this;
          upper = g->upper;

          g->Set(c, d);
          p->Set(b, g);
          Set(a, p);
        }
        break;
        }
      } while (upper != nullptr);
      return this;
    } // end of 'splay'
  };

  Node *root = nullptr;

  void FindGreaterEq(const std::size_t &key)
  {
    std::size_t accum = 0;
    if (root == nullptr)
      return;
    Node
      *cur = root,
      *bestMatch = nullptr;
    do
    {
      if (cur->LeftEq(accum) == key)
      {
        root = cur->Splay();
        return;
      }
      if (cur->LeftEq(accum) > key)
      {
        bestMatch = cur;
        cur = cur->left;
      }
      else
      {
        if (cur->right == nullptr && bestMatch == nullptr)
        {
          root = cur->Splay();
          return;
        }
        accum = cur->LeftEq(accum);
        cur = cur->right;
      }
    } while (cur != nullptr);
    root = bestMatch->Splay();
  }

  Node * Find(const std::size_t &key)
  {
    if (root == nullptr)
      return nullptr;
    FindGreaterEq(key);
    if (root->LeftEq() != key)
      return nullptr;

    return root;
  }

  void Add(const std::size_t &key, const ValueType &data)
  {
    if (root == nullptr)
    {
      auto cur = new Node(0); // 1
      for (std::size_t i = 2; i <= key; i++)
      {
        auto next = new Node(0);
        next->Set(cur, nullptr);
        cur = next;
      }
      cur->data = data;
      root = cur;
      return;
    }
    FindGreaterEq(key);
    if (root->LeftEq() == key)
    {
      auto
        l = root->left,
        r = root;
      r->left = nullptr;
      r->UpdateKey();
      root = new Node(data);
      root->Set(l, r);
    }
    else if (root->LeftEq() < key)
    {
      auto cur = new Node(0);
      cur->Set(root, nullptr);
      for (std::size_t i = root->key + 2; i <= key; i++)
      {
        auto next = new Node(0);
        next->Set(cur, nullptr);
        cur = next;
      }
      cur->data = data;
      root = cur;
      return;
    }
    else // >
      throw "up";
  }

  void Del(Node *node)
  {
    if (node == nullptr)
      return;
    root = node->Splay();
    auto
      l = root->left,
      r = root->right;
    if (l != nullptr)
      l->upper = nullptr;
    if (r != nullptr)
      r->upper = nullptr;
    root->Set(nullptr, nullptr);
    delete root;
    if (l == nullptr)
    {
      root = r;
      return;
    }

    if (r == nullptr)
    {
      root = l;
      return;
    }
    while (r->left != nullptr)
      r = r->left;
    r->Set(l, r->right);
    root = r->Splay();
  }

  ~ImplicitSplayTree(void)
  {
    FreePtr(root);
  }
};

int main(void)
{
#ifdef _DEBUG
  freopen("input.txt", "r", stdin);
  // freopen("splay.txt", "w", stdout);
#endif
  ImplicitSplayTree<int> tree;
  unsigned m = 0, n0 = 0;

  scanf("%u %u", &n0, &m);

  for (unsigned c = 0; c < n0; c++)
  {
    int x;
    scanf("%i", &x);
    tree.Add(c + 1, x);
  }

  scanf("\n");

  for (unsigned c = 0; c < m; c++)
  {
    int i, x;
    if (scanf("add %i %i\n", &i, &x) == 2)
      tree.Add(i + 1, x);
    else if (scanf("del %i\n", &i) == 1)
      tree.Del(tree.Find(i));
    else
      throw "up";
  }

  if (tree.root == nullptr)
  {
    printf("0\n");
    return 0;
  }

  {
    auto cur = tree.root;
    while (cur->left != nullptr)
      cur = cur->left;
    tree.root = cur->Splay();
  }
  printf("%u\n", tree.root->key);
  while (true)
  {
    printf("%i ", tree.root->data);
    if (tree.root->right == nullptr)
      break;
    tree.FindGreaterEq(tree.root->LeftEq() + 1);
  }
  if (tree.root->right != nullptr)
    throw "up";
  return 0;
}
