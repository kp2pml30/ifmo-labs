#define _CRT_SECURE_NO_WARNINGS

/*
          .__....._             _.....__,
            .": o :':         ;': o :".
            `. `-' .'.       .'. `-' .'
              `---'             `---'

    _...----...      ...   ...      ...----..._
 .-'__..-""'----    `.  `"`  .'    ----'""-..__`-.
'.-'   _.--"""'       `-._.-'       '"""--._   `-.`
'  .-"'                  :                  `"-.  `
  '   `.              _.'"'._              .'   `
        `.       ,.-'"       "'-.,       .'
          `.                           .'
            `-._                   _.-'
                `"'--...___...--'"`
*/

#include <cstdio>
#include <utility>
#include <tuple>

#include <algorithm>

#include <vector>

using BlankType = std::tuple<>;

#ifdef _DEBUG
# define UseTreeType int
#else
# define UseTreeType BlankType
#endif

template<typename KeyType>
static void FreePtr(KeyType *& ptr)
{
  if (ptr != nullptr)
  {
    delete ptr;
    ptr = nullptr;
  }
}

#define CYCLED ((ImplicitSplayTree<UseTreeType>::Node *)1)

template<typename ValueType>
class ImplicitSplayTree
{
private:
public:
  class Node
  {
  public:
    std::size_t key;
    ValueType data;
    Node
      *upper = nullptr,
      *left = nullptr,
      *right = nullptr;

    bool flip = false;

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

    void PropUppers(void)
    {
      if (this == nullptr || this == CYCLED)
        return;
      upper->PropUppers();
      Propagate();
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

    std::size_t RightEq(std::size_t accum = 0)
    {
      return accum + 1 + (right == nullptr ? 0 : right->key);
    }

    Node * Splay(void)
    {
      // already upper
      if (upper == nullptr || upper == CYCLED)
        return this;
      PropUppers();
      do
      {
        // zig
        if (upper->upper == nullptr || upper->upper == CYCLED)
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
          if (g->upper != nullptr && g->upper != CYCLED)
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
          if (g->upper != nullptr && g->upper != CYCLED)
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
          if (g->upper != nullptr && g->upper != CYCLED)
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
          if (g->upper != nullptr && g->upper != CYCLED)
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
      } while (upper != nullptr && upper != CYCLED);
      return this;
    } // end of 'splay'
  };

  static Node * Merge(Node *l, Node *r)
  {
    if (l == nullptr) return r;
    if (r == nullptr) return l;
    // if !(r belongs l) they are different
    l->Splay();
    if (l->upper == CYCLED)
      throw "illegal task";
    r->Splay();
    if (r->upper == CYCLED)
      throw "illegal task";
    // cycle check
    if (l->upper == r || l->upper != nullptr && l->upper->upper == r)
    {
      r->upper = CYCLED;
      return r;
    }
    // they are different
    if (r->left == nullptr)
      if (l->right == nullptr)
        r->Set(l, r->right);
      else
        l->flip = 1, r->Set(l, r->right);
    else if (r->right == nullptr)
      if (l->left == nullptr)
        r->Set(r->left, l);
      else
        l->flip = 1, r->Set(r->left, l);
    else
      throw "up";
    return r;
  }

  static void Detatch(Node *i, Node *j)
  {
    i->Splay();
    {
      // hide declarations
      auto fromI = i->RightEq();
      j->Splay();
      auto fromJ = j->RightEq();
      if (fromJ > fromI)
        std::swap(i, j);
      // now i --- j
    }
    i->Splay();
    bool outerFlag = (i->left == nullptr);
    j->Splay();
    outerFlag = outerFlag && (j->right == nullptr);
    i->Splay();
    // set to null anyway
    const auto prevRoot = i->upper;
    i->upper = nullptr;

    // if it is [---i....j---]
    if (prevRoot == CYCLED && outerFlag)
      return;


    // breaks cycle
    if (i->right != nullptr)
      i->right->upper = nullptr;
    i->Set(i->left, nullptr);
    j->Splay();

    if (prevRoot == CYCLED)
    {
      while (i->left != nullptr)
        i = i->left;
      i->Set(j, i->right);
    }
  }
};

#include <iostream>

using std::cin;

int main(void)
{
#ifdef _DEBUG
  freopen("input.txt", "r", stdin);
  // freopen("splay.txt", "w", stdout);
#endif
  using Tree = ImplicitSplayTree<UseTreeType>;
  using Node = Tree::Node;

  unsigned m = 0, n = 0, q = 0;

  cin >> n >> m >> q;

  std::vector<Node *> jungle(n + 1);
  for (unsigned c = 1; c <= n; c++)
    jungle[c] = new Node(
#ifdef _DEBUG
      c
#else
      BlankType()
#endif
    );
  for (unsigned c = 0; c < m; c++)
  {
    unsigned i = 0, j = 0;
    cin >> i >> j;
    Tree::Merge(jungle[i], jungle[j]);
  }

  for (unsigned c = 0; c < q; c++)
  {
    cin >> std::ws;
    unsigned i = 0, j = 0;
    char oper;
    cin >> oper >> i >> j;
    if (oper == '+')
    {
      Tree::Merge(jungle[i], jungle[j]);
    }
    else if (oper == '-')
    {
      Tree::Detatch(jungle[i], jungle[j]);
      // jungle[i]->Splay();
    }
    else if (oper == '?')
    {
      if (i == j)
      {
        printf("0\n");
        continue;
      }
      auto
        &l = jungle[i],
        &r = jungle[j];
      l->Splay();
      auto inl = l->RightEq();
      r->Splay();
      if (l->upper == r || l->upper != nullptr && l->upper != CYCLED && l->upper->upper == r)
      {
        auto rRe = r->RightEq();
        auto ansApprox = std::max(inl, rRe) - std::min(inl, rRe) + 1;
        if (r->upper == CYCLED)
          printf("%u\n", std::min(ansApprox - 2, r->key - ansApprox));
        else
          printf("%u\n", ansApprox - 2);
      }
      else
        printf("-1\n");
    }
    else
      break; // throw "up";
  }

  // no memory cleaning :(
  return 0;
}

/*
               ...
             ;::::;
           ;::::; :;
         ;:::::'   :;
        ;:::::;     ;.
       ,:::::'       ;           OOO\
       ::::::;       ;          OOOOO\
       ;:::::;       ;         OOOOOOOO
      ,;::::::;     ;'         / OOOOOOO
    ;:::::::::`. ,,,;.        /  / DOOOOOO
  .';:::::::::::::::::;,     /  /     DOOOO
 ,::::::;::::::;;;;::::;,   /  /        DOOO
;`::::::`'::::::;;;::::: ,#/  /          DOOO
:`:::::::`;::::::;;::: ;::#  /            DOOO
::`:::::::`;:::::::: ;::::# /              DOO
`:`:::::::`;:::::: ;::::::#/               DOO
 :::`:::::::`;; ;:::::::::##                OO
 ::::`:::::::`;::::::::;:::#                OO
 `:::::`::::::::::::;'`:;::#                O
  `:::::`::::::::;' /  / `:#
   ::::::`:::::;'  /  /   `#

______ _____  ___ ______   _____ _   _  _____ ___________ _____
|  _  \  ___|/ _ \|  _  \ |_   _| \ | |/  ___|_   _|  _  \  ___|
| | | | |__ / /_\ \ | | |   | | |  \| |\ `--.  | | | | | | |__
| | | |  __||  _  | | | |   | | | . ` | `--. \ | | | | | |  __|
| |/ /| |___| | | | |/ /   _| |_| |\  |/\__/ /_| |_| |/ /| |___
|___/ \____/\_| |_/___/    \___/\_| \_/\____/ \___/|___/ \____/
*/


