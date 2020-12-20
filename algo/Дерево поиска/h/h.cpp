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
    bool flip = false;

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

    void Propagate(void)
    {
      if (flip)
      {
        std::swap(left, right);
        if (left != nullptr) left->flip ^= 1;
        if (right != nullptr) right->flip ^= 1;
        flip = false;
      }
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
      cur->Propagate();
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

  void FindLessEq(const std::size_t &data)
  {
    if (root == nullptr)
      return;
    std::size_t accum = 0;
    Node
      *cur = root,
      *bestMatch = nullptr;
    do
    {
      cur->Propagate();
      if (cur->LeftEq(accum) == data)
      {
        root = cur->Splay();
        return;
      }
      if (cur->LeftEq(accum) > data)
      {
        if (cur->left == nullptr && bestMatch == nullptr)
        {
          root = cur->Splay();
          return;
        }
        cur = cur->left;
      }
      else
      {
        accum += cur->LeftEq();
        bestMatch = cur;
        cur = cur->right;
      }
    } while (cur != nullptr);
    root = bestMatch->Splay();
  }

  // no need to change
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

  static Node * Merge(Node *l, Node *r)
  {
    if (l == nullptr) return r;
    if (r == nullptr) return l;
    l->Propagate();
    while (l->right != nullptr)
      l = l->right, l->Propagate();
    l = l->Splay();
    l->Set(l->left, r);
    return l;
  }

  ~ImplicitSplayTree(void)
  {
    FreePtr(root);
  }
};

template<typename typ>
void PrintTree(typ &tree)
{
  {
    auto cur = tree.root;
    cur->Propagate();
    while (cur->left != nullptr)
    {
      cur = cur->left;
      cur->Propagate();
    }
    tree.root = cur->Splay();
  }
  while (true)
  {
    printf("%i ", tree.root->data);
    if (tree.root->right == nullptr)
      break;
    tree.FindGreaterEq(tree.root->LeftEq() + 1);
  }
  printf("\n");
  if (tree.root->right != nullptr)
    throw "up";
}

int main(void)
{
#ifdef _DEBUG
  freopen("input.txt", "r", stdin);
  freopen("splay.txt", "w", stdout);
#endif
  ImplicitSplayTree<int> tree;
  unsigned m = 0, n = 0;

  scanf("%u %u", &n, &m);
  for (unsigned i = 1; i <= n; i++)
    tree.Add(i, i);

  for (unsigned c = 0; c < m; c++)
  {
    // PrintTree(tree);

    unsigned l, r;
    scanf("%u %u", &l, &r);
    if (l == r)
      continue;
    tree.FindGreaterEq(l);
    auto beg = tree.root;
    tree.FindLessEq(r);
    /* possible only:
     *      r
     *     /
     *    .
     *   /
     *  l
     *
     *     r
     *    /
     *   l
     *
     * WORKS ANYWAY!
     */
    auto end = tree.root;
    auto
      a = beg->left,
      b = end->right;
    if (a != nullptr) a->upper = nullptr;
    if (b != nullptr) b->upper = nullptr;
    end->Set(end->left, nullptr);
    beg->Set(nullptr, beg->right);
    beg = beg->Splay();

    beg->flip ^= 1;

    tree.root = tree.Merge(a, tree.Merge(beg, b));
  }

  PrintTree(tree);
  return 0;
}
