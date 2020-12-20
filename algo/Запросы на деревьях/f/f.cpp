#include <vector>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <fstream>
#include <functional>
#include <memory>
#include <map>
#include <unordered_map>

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
10
-1 1 2 1 3 1 4 7 4 3
1
6 7 4 8 9 7 6
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
// auto cin = std::ifstream("minonpath.in");
// auto cout = std::ofstream("minonpath.out");
#endif

constexpr auto min_neutral = std::numeric_limits<std::int32_t>::max();

std::uint64_t path_id_counter = 0;

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
      *left = nullptr,
      *right = nullptr;

    struct
    {
      bool isRoot = true;
      union
      {
        std::size_t index = 0;
        Node *upper;
      };
      std::size_t path_id = path_id_counter++;
    } upper_data;


    std::size_t key;
    ValueType data;

    Node(const ValueType data) : key(1), data(data) {}

    /*
    ~Node(void)
    {
      FreePtr(left);
      FreePtr(right);
    }
    */

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
      // UpdateKey();
    }

    void UpdateKey(void)
    {
      key = 1
        + (left  == nullptr ? 0 : left ->key)
        + (right == nullptr ? 0 : right->key)
        ;
    }

    Node * Splay(void)
    {
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
  std::ios_base::sync_with_stdio(false);
  cin.tie(nullptr);

  std::size_t n;
  cin >> n;
  std::vector<std::shared_ptr<NodeType>> tree;
  tree.push_back(std::shared_ptr<NodeType>(new NodeType(0)));
  for (std::size_t i = 1; i <= n; i++)
  {
    int upper;
    cin >> upper;
    tree.push_back(std::shared_ptr<NodeType>(new NodeType(i)));
    tree.back()->upper_data.isRoot = true;
    tree.back()->upper_data.index = (upper == -1 ? 0 : upper);
  }

  auto expose = [&](NodeType *node) {
    while (true)
    {
      node->Splay();
      if (node->upper_data.index == 0)
      {
        node->upper_data.path_id = path_id_counter++;
        return;
      }
      NodeType *n2 = tree[node->upper_data.index].get();
      n2->Splay();
      if (n2->left != nullptr)
      {
        n2->left->upper_data.isRoot = true;
        n2->left->upper_data.index = n2->data;
        n2->left->upper_data.path_id = path_id_counter++;
        n2->left = nullptr;
      }
      n2->SetLeft(node);
    }
  };

  std::size_t m;
  cin >> m;
  std::vector<std::size_t> group;
  std::unordered_map<std::size_t, std::size_t> was;
  group.reserve(n + 1);

  for (std::size_t i = 0; i < m; i++)
  {
    was.clear();
    std::size_t group_size;
    cin >> group_size;
    group.resize(group_size);
    for (std::size_t j = 0; j < group_size; j++)
    {
      cin >> group[j];
      expose(tree[group[j]].get());
    }

    if (group_size == n)
    {
      cout << n << '\n';
      continue;
    }

    
    std::size_t ans = 0;
    for (auto &j : group)
    {
      auto node = tree[j].get();
      node->Splay();

      std::size_t cur_ans = 1;
      if (node->right != nullptr)
        cur_ans += node->right->key;

      auto &saved = was[node->upper_data.path_id];
      if (saved >= cur_ans)
        continue;

      ans += cur_ans - saved;
      saved = cur_ans;
    }
    cout << ans << '\n';
  }
  cout << std::flush;
  return 0;
}