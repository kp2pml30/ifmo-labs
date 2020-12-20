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
    Type count;

    Node(const Type &data) : data(data), count(1) {}

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
      count = 1
        + (left  == nullptr ? 0 : left ->count)
        + (right == nullptr ? 0 : right->count)
        ;
    }

    int RightCount(int accum = 0)
    {
      return accum + 1 + (right == nullptr ? 0 : right->count);
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

  void Del(Node *nd)
  {
    if (nd == nullptr)
      return;
    root = nd->Splay();
    Node
      *left  = root->left,
      *right = root->right;
    root->Set(nullptr, nullptr);
    delete root;
    if (left == nullptr)
    {
      if (right != nullptr) right->upper = nullptr;
      root = right;
      return;
    }
    if (right == nullptr)
    {
      left->upper = nullptr;
      root = left;
      return;
    }
    left->upper = nullptr;
    right->upper = nullptr;
    while (left->right != nullptr)
      left = left->right;
    left->Set(left->left, right);
    root = right->Splay();
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
  SplayTree<int> tree;
  int n;
  bool hasLast = false;

  scanf("%i\n", &n);

  for (int i = 0; i < n; i++)
  {
    int prog, x;
    scanf("%i %i", &prog, &x);
    if (prog == -1)
      tree.Del(tree.Find(x));
    else if (prog == 0)
    {
      auto cur = tree.root;
      while (true)
      {
        if (cur->RightCount() < x)
        {
          x -= cur->RightCount();
          cur = cur->left;
        }
        else if (cur->RightCount() == x)
        {
          printf("%i\n", cur->data);
          tree.root = cur->Splay();
          break;
        }
        else
        {
          cur = cur->right;
        }
      }
    }
    else
      tree.Add(x);
  }

  return 0;
}
