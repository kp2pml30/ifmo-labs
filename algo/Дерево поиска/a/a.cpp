#define _CRT_SECURE_NO_WARNINGS

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

    Node(const Type &data) : data(data) {}

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

            Set(p, d);
            p->Set(g, c);
            g->Set(a, b);
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

            Set(g, p);
            g->Set(a, b);
            p->Set(c, d);
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

            Set(p, g);
            p->Set(a, b);
            g->Set(c, d);
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

            Set(a, p);
            p->Set(b, g);
            g->Set(c, d);
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
      root->left = nullptr;
      return {left, root};
    }
    else
    {
      auto right = root->right;
      if (right != nullptr) right->upper = nullptr;
      root->right = nullptr;
      return {root, right};
    }
  }

  Node * Merge(Node *l, Node *r)
  {
    if (l == nullptr)
      return r;

    while (l->right != nullptr)
      l = l->right;
    l->Splay();
    l->SetRight(r);
    return l;
  }

  void Add(const Type &data)
  {
    FindGreaterEq(data);
    if (root != nullptr && root->data == data)
      return;
    auto [l, r] = Split(data);
    root = new Node(data);
    root->Set(l, r);
  }

  void Del(const Type &data)
  {
    if (root == nullptr)
      return;
    FindGreaterEq(data);
    if (root->data == data)
    {
      auto
        l = root->left,
        r = root->right;
      if (l != nullptr)
        l->upper = nullptr;
      if (r != nullptr)
        r->upper = nullptr;
      root->left = nullptr;
      root->right = nullptr;
      delete root;
      root = Merge(l, r);
    }
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
  freopen("splay.txt", "w", stdout);
#endif
  SplayTree<int> tree;
  int x;

  while (true)
  {
    if (scanf("insert %i\n", &x) == 1)
      tree.Add(x);
    else if (scanf("delete %i\n", &x) == 1)
      tree.Del(x);
    else if (scanf("exists %i\n", &x) == 1)
      printf("%s\n", tree.Find(x) != nullptr ? "true" : "false");
    else if (scanf("next %i\n", &x) == 1)
    {
      tree.FindGreaterEq(x);
      if (tree.root == nullptr)
        printf("none\n");
      else if (tree.root->data != x)
      {
        if (tree.root->data < x)
          printf("none\n");
        else
          printf("%i\n", tree.root->data);
      }
      else
        if (tree.root->right == nullptr)
          printf("none\n");
        else
        {
          auto cur = tree.root->right;
          while (cur->left != nullptr)
            cur = cur->left;
          printf("%i\n", cur->data);
        }
    }
    else if (scanf("prev %i\n", &x) == 1)
    {
      tree.FindGreaterEq(x);
      if (tree.root == nullptr)
        printf("none\n");
      else if (tree.root->data < x)
      {
        auto cur = tree.root;
        while (cur->right != nullptr)
          cur = cur->right;
        printf("%i\n", cur->data);
      }
      else if (tree.root->left == nullptr)
        printf("none\n");
      else
      {
        auto cur = tree.root->left;
        while (cur->right != nullptr)
          cur = cur->right;
        printf("%i\n", cur->data);
      }
    }
    else
      break;
  }

  return 0;
}
