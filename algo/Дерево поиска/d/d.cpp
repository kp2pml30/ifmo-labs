#if 1
#define _CRT_SECURE_NO_WARNINGS
#include <cstdint>
#include <cinttypes>

/*
                       _
                      \`*-.
                       )  _`-.
                      .  : `. .
                      : _   '  \
                      ; *` _.   `*-._
                      `-.-'          `-.
                        ;       `       `.
                        :.       .        \
                        . \  .   :   .-'   .
                        '  `+.;  ;  '      :
                        :  '  |    ;       ;-.
                        ; '   : :`-:     _.`* ;
               [bug] .*' /  .*' ; .*`- +'  `*'
                     `*-*   `*-*  `*-*'
*/

#include <cstdio>
#include <utility>

template<typename Type>
static void FreePtr(Type *& ptr)
{
  if (ptr != nullptr)
  {
    delete ptr;
    ptr = nullptr;
  }
}

template<typename Type>
class SplayTree
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
    Type data;
    Type sum;

    Node(const Type &data) : data(data), sum(data) {}

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
      sum = data
        + (left == nullptr ? 0 : left->sum)
        + (right == nullptr ? 0 : right->sum)
        ;
    }

    Type sumR(void)
    {
      return data + (right == nullptr ? 0 : right->sum);
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

  void FindGreaterEq(const Type &data)
  {
    if (root == nullptr)
      return;
    Node
      *cur = root,
      *bestMatch = nullptr;
    do
    {
      if (cur->data == data)
      {
        root = cur->Splay();
        return;
      }
      if (cur->data > data)
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
        cur = cur->right;
      }
    } while (cur != nullptr);
    root = bestMatch->Splay();
  }

  void FindLessEq(const Type &data)
  {
    if (root == nullptr)
      return;
    Node
      *cur = root,
      *bestMatch = nullptr;
    do
    {
      if (cur->data == data)
      {
        root = cur->Splay();
        return;
      }
      if (cur->data > data)
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
        bestMatch = cur;
        cur = cur->right;
      }
    } while (cur != nullptr);
    root = bestMatch->Splay();
  }

  Node * Find(const Type &data)
  {
    if (root == nullptr)
      return nullptr;
    FindGreaterEq(data);
    if (root->data != data)
      return nullptr;

    return root;
  }

  std::pair<Node *, Node *> Split(const Type &data)
  {
    if (root == nullptr)
      return {nullptr, nullptr};
    FindGreaterEq(data);
    if (root->data > data)
    {
      auto left = root->left;
      if (left != nullptr) left->upper = nullptr;
      root->Set(nullptr, root->right);
      return {left, root};
    }
    else
    {
      auto right = root->right;
      if (right != nullptr) right->upper = nullptr;
      root->Set(root->left, nullptr);
      return {root, right};
    }
  }

  void Add(const Type &data)
  {
    FindGreaterEq(data);
    if (root != nullptr && root->data == data)
      return;
    auto pai = Split(data);
    root = new Node(data);
    root->Set(pai.first, pai.second);
  }

  ~SplayTree(void)
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
  SplayTree<std::uint64_t> tree;
  int n;
  int l, r;
  bool hasLast = false;
  std::uint64_t last = 0;

  scanf("%i\n", &n);

  while (true)
  {
    if (scanf("+ %i\n", &l) == 1)
    {
      if (hasLast)
        tree.Add((last + l) % 1000000000);
      else
        tree.Add(l);
      hasLast = false;
      last = 0;
    }
    else if (scanf("? %i %i\n", &l, &r) == 2)
    {
      hasLast = true;
      last = 0;
      tree.FindGreaterEq(l);
      if (tree.root == nullptr || tree.root->data > r || tree.root->data < l)
      {
        printf("0\n");
        continue;
      }
      auto a1 = tree.root->sumR();
      auto prevroot = tree.root;
      tree.FindLessEq(r);
      if (tree.root == prevroot)
        last = tree.root->data;
      else
        last = a1 - tree.root->sumR() + tree.root->data;
      printf("%" PRIu64 "\n", last);
    }
    else
      break;
  }

  return 0;
}

#else
// #pragma comment(linker, "/STACK:36777216")
#define _CRT_SECURE_NO_WARNINGS

#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdio>
#include <fstream>

using uint = unsigned;

#if !defined(__OPTIMIZE__)
#	include <sstream>
auto cin = std::stringstream(R"delim(
1232424
+ 0
? 0 0
+ 5
? 0 10000
? 5 6
? 5 5
? 4 5
? 6 6
)delim");
#else
using std::cin;
// std::ifstream cin("crypto.in");
#endif

// i won't clean memory because this task is awful

struct container
{
  std::uint64_t full;

  container operator+(const container &r) const
  {
    container ret;
    ret.full = full + r.full;
    return ret;
  }

  container(std::uint64_t v = 0) : full(v) {}

  bool operator==(const container &r) const { return full == r.full; }
};

static const container setn = container(0);

container SetCombine(container l, container r)
{
  if (r == setn)
    return l;
  return r;
}
container SetCombine(container l, container r, int lx, int rx)
{
  if (r == setn)
    return l;
  if (l == setn)
    return r;
  int m = rx - lx;
  r.full *= m;
  return r;
}

class Tree
{
public:
  class Node
  {
  private:
    friend Tree;
    void Split(int lx, int rx)
    {
      if (rx - lx == 1)
        return;
      const int m = lx + (rx - lx) / 2;
      left = new Node();
      right = new Node();
      uint64_t delta = el.full / (rx - lx);
      left->el.full = delta * (m - lx);
      right->el.full = delta * (rx - m);
      // left->Split(lx, m);
      // right->Split(m, rx);
    }
  public:
    Node
      *left = nullptr,
      *right = nullptr;

    container
      el;

    void Set(int l, int r, container v, int lx, int rx)
    {
      if (l >= rx || lx >= r)
        return;
      if (lx >= l && rx <= r)
      {
        el = SetCombine(el, v, lx, rx);
        return;
      }
      if (left == nullptr)
        Split(lx, rx);
      int m = lx + (rx - lx) / 2;
      left->Set(l, r, v, lx, m);
      right->Set(l, r, v, m, rx);
      el = left->el + right->el;
    }

    container calc(int l, int r, int lx, int rx)
    {
      if (l >= rx || lx >= r)
        return container();
      if (lx >= l && rx <= r)
        return el;
      if (left == nullptr)
      {
        uint64_t delta = el.full / (rx - lx);
        uint64_t vvv = ((int)(r < rx ? r : rx) - (int)(l > lx ? l : lx)) * delta;
        return container(vvv);
      }
      auto m = lx + (rx - lx) / 2;
      return left->calc(l, r, lx, m) + right->calc(l, r, m, rx);
    }
  };

  Node *head;
  int n;

  Tree(int n)
  {
    n--;
    n |= n >> 1;
    n |= n >> 2;
    n |= n >> 4;
    n |= n >> 8;
    n |= n >> 16;
    n++;
    this->n = n;
    head = new Node();
    // head->Split(0, n);
  }

  void Set(int l, int r, container v) { head->Set(l, r, v, 0, n); }
  container Get(int l, int r) { return head->calc(l, r, 0, n); }
};


int main(void)
{
  int n;
  cin >> n;
  Tree tree(1000000000);
  std::uint64_t last = 0;
  bool hasLast = false;
  while (!cin.eof())
  {
    std::string str;
    while (!cin.eof() && cin.peek() != '\n')
      str.push_back(cin.get());
    if (cin.eof())
      break;
    cin.get();
    if (str.empty())
      continue;
    uint l, r;
    if (sscanf(str.c_str(), "+ %u", &l) == 1)
    {
      auto val = hasLast ? (last + l) % 1000000000 : l;
      tree.Set(val, val + 1, container({val}));
      hasLast = false;
    }
    else if (sscanf(str.c_str(), "? %u %u", &l, &r) == 2)
    {
      last = tree.Get(l, r + 1).full;
      hasLast = true;
      printf("%u\n", last);
    }
    else
      return 0;
  }
  return 0;
}
#endif
