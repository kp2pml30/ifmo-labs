#pragma once

#include <cassert>
#include <type_traits>
#include <utility>

#include <string>

template <typename T, typename C>
static constexpr bool is_nothrow_comparable_v = noexcept(
    std::declval<C>()(std::declval<T const &>(), std::declval<T const &>()));

namespace splay {
template <typename T> struct default_tag_t {};
template <typename T> struct default_tag2_t {};

/**
 * tree holder with splay operation
 * said to be const, since every operation over splay is not const under the
 * hood
 */
template <typename Tag> struct splay_node {
  mutable splay_node *left = nullptr, *right = nullptr, *up = nullptr;

#if 0
    template<splay_node* splay_node::* getter>
    static constexpr splay_node* splay_node::* cogetter_v =  getter ^ &splay_node::left ^ &splay_node::right;
#else
  template <splay_node *splay_node::*getter>
  static constexpr splay_node *splay_node::*cogetter_f() noexcept {
    if constexpr (getter == &splay_node::left)
      return &splay_node::right;
    else if constexpr (getter == &splay_node::right)
      return &splay_node::left;
    else
      return ""; // generate error, static assert fails anyway
  }
  template <splay_node *splay_node::*getter>
  static constexpr auto cogetter_v = cogetter_f<getter>();
#endif

private:
  template <splay_node *splay_node::*getter> void rotate() const noexcept {
    constexpr auto cogetter = cogetter_v<getter>;
    auto p = up;
    auto r = this->*cogetter;
    if (p != nullptr) {
      if (p->*getter == this)
        p->*getter = r;
      else
        p->*cogetter = r;
    }
    auto unconst_this = const_cast<splay_node *>(this);
    auto tmp = r->*getter;
    r->*getter = unconst_this;
    unconst_this->*cogetter = tmp;

    up = r;
    r->up = p;
    if (auto got = this->*cogetter; got != nullptr)
      got->up = const_cast<splay_node *>(this);
  }

public:
  splay_node const *splay() const noexcept {
    while (up != nullptr)
      if (this == up->left) {
        if (up->up == nullptr) {
          up->rotate<&splay_node::right>();
        } else if (up == up->up->left) {
          up->up->template rotate<&splay_node::right>();
          up->rotate<&splay_node::right>();
        } else {
          up->rotate<&splay_node::right>();
          up->rotate<&splay_node::left>();
        }
      } else {
        if (up->up == nullptr) {
          up->rotate<&splay_node::left>();
        } else if (up == up->up->right) {
          up->up->template rotate<&splay_node::left>();
          up->rotate<&splay_node::left>();
        } else {
          up->rotate<&splay_node::left>();
          up->rotate<&splay_node::right>();
        }
      }
    return this;
  }

  template <splay_node *splay_node::*getter>
  splay_node const *left_right_most() const noexcept {
    auto cur = this;
    while (cur->*getter != nullptr)
      cur = cur->*getter;
    return cur->splay();
  }

  template <splay_node *splay_node::*getter>
  splay_node const *next_prev_impl() const noexcept {
    constexpr auto cogetter = cogetter_v<getter>;
    if (auto r = this->*getter; r != nullptr)
      return r->template left_right_most<cogetter>();
    if (up == nullptr)
      return nullptr;
    auto prev = this;
    auto cur = up;
    while (cur != nullptr && cur->*getter == prev) {
      prev = cur;
      cur = cur->up;
    }
    return cur ?: prev;
  }
  splay_node const *next() const noexcept {
    return next_prev_impl<&splay_node::right>();
  }
  splay_node const *prev() const noexcept {
    return next_prev_impl<&splay_node::left>();
  }

  splay_node const *left_most() const noexcept {
    return left_right_most<&splay_node::left>();
  }
  splay_node const *right_most() const noexcept {
    return left_right_most<&splay_node::right>();
  }

  /**
   * cuts as {[0..cur), [cur..end]}
   */
  std::pair<splay_node const *, splay_node const *> cut() const noexcept {
    splay();
    auto l = left;
    if (left != nullptr) {
      left->up = nullptr;
      left = nullptr;
    }
    return {l, this};
  }
  /**
   * cuts as {[0..cur), cur, (cur..end]}
   */
  std::tuple<splay_node const *, splay_node const *, splay_node const *>
  cutcut() const noexcept {
    auto [l, c] = cut();
    auto r = c->right;
    if (c->right != nullptr) {
      c->right->up = nullptr;
      c->right = nullptr;
    }
    return {l, c, r};
  }
  template <splay_node *splay_node::*getter>
  void merge_side(splay_node const *tree) const noexcept {
    if (tree == nullptr)
      return;
    assert(tree->up == nullptr);
    splay();
    auto cur = left_right_most<getter>();
    const_cast<splay_node *>(cur)->*getter = const_cast<splay_node *>(tree);
    if (tree != nullptr)
      tree->up = const_cast<splay_node *>(cur);
    splay();
  }
  void merge_l(splay_node const *tree) const noexcept {
    merge_side<&splay_node::left>(tree);
  }
  void merge_r(splay_node const *tree) const noexcept {
    merge_side<&splay_node::right>(tree);
  }
  void merge(splay_node const *treel, splay_node const *treer) const noexcept {
    merge_l(treel);
    merge_r(treer);
  }

  /**
   * cuts detatches current alement from tree
   */
  splay_node const *cutcutmerge() const noexcept {
    auto [l, cur, r] = cutcut();
    if (r == nullptr)
      return l;
    r->merge_l(l);
    return r;
  }
};

template <typename T, typename Tag = default_tag_t<T>>
class splay_holder : public splay_node<void> {
public:
  using node_t = splay_node<void>;
  using value_type = T;

  T data;

  explicit splay_holder(T const &data) noexcept(
      std::is_nothrow_constructible_v<T, T const &>)
      : data(data) {}
  explicit splay_holder(T &&data) noexcept(
      std::is_nothrow_constructible_v<T, T &&>)
      : data(std::move(data)) {}

  constexpr node_t const *as_node() const noexcept {
    return static_cast<node_t const *>(this);
  }

  static splay_holder const *cast(node_t const *from) noexcept {
    if (from == nullptr)
      return nullptr;
    return static_cast<splay_holder const *>(from);
  }

  template <typename F, typename... A>
  splay_holder const *call(F f, A &&... a) const noexcept {
    return cast((this->*f)(std::forward<A>(a)...));
  }

  template <typename C>
  splay_holder const *find_ge(T const &e, C const &c) const
      noexcept(is_nothrow_comparable_v<T, C>) {
    this->splay();
    splay_holder const *cur = this;
    splay_holder const *best = nullptr;
    do {
      auto const &cd = cast(cur)->data;
      if (c(e, cd)) {
        best = cur;
        cur = cast(cur->left);
      } else if (!c(cd, e)) // eq
      {
        return cast(cur->splay());
      } else {
        if (cur->right == nullptr) {
          if (best == nullptr)
            return nullptr;
          else
            return cast(best->splay());
        }
        cur = cast(cur->right);
      }
    } while (cur != nullptr);
    if (best == nullptr)
      return nullptr;
    return cast(best->splay());
  }

  /**
   * debug functions which ports graph to mermaid
   * add `graph TD` line before output
   */
  std::string to_mermaid(int &counter, std::string &res) const noexcept {
    auto mestr = std::to_string(counter++);
    if (this == nullptr) {
      res += "_" + mestr + "[nil];\n";
      return mestr;
    }
    res += "_" + mestr + "[" + std::to_string(data) + "];\n";
    res += "_" + mestr + " ---> _" +
           cast(node_t::left)->ToMermaid(counter, res) + ";\n";
    res += "_" + mestr + " ---> _" +
           cast(node_t::right)->ToMermaid(counter, res) + ";\n";
    return mestr;
  }
};
} // namespace splay
