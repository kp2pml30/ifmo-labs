#pragma once

#include <exception>
#include <functional>
#include <stdexcept>

#include <iostream>
#include <type_traits>
#include <utility>

#include "bimap-helper.h"
#include "splay.h"

template <typename Left, typename Right, typename CompareLeft = std::less<Left>,
          typename CompareRight = std::less<Right>>
struct bimap
    : private bimap_helper::tagged_comparator<CompareLeft>,
      private bimap_helper::tagged_comparator<
          CompareRight, bimap_helper::second_tag<CompareLeft, CompareRight>> {
  using left_t = Left;
  using right_t = Right;

private:
  using node_t = bimap_helper::node_t<Left, Right>;
  using left_comparator_holder = bimap_helper::tagged_comparator<CompareLeft>;
  using right_comparator_holder = bimap_helper::tagged_comparator<
      CompareRight, bimap_helper::second_tag<CompareLeft, CompareRight>>;

  template <typename T>
  using iterator_from_node_type = bimap_helper::bimap_iterator<node_t, T>;

public:
  using left_iterator = iterator_from_node_type<typename node_t::left_holder>;
  using right_iterator = iterator_from_node_type<typename node_t::right_holder>;

private:
  template <typename T>
  using co_iterator = std::conditional_t<std::is_same_v<left_iterator, T>,
                                         right_iterator, left_iterator>;

  node_t const *root;
  std::size_t sz;

  CompareLeft const &left_comparator() const noexcept {
    return static_cast<CompareLeft const &>(
        static_cast<left_comparator_holder const &>(*this));
  }
  CompareRight const &right_comparator() const noexcept {
    return static_cast<CompareRight const &>(
        static_cast<right_comparator_holder const &>(*this));
  }

  template <typename T>
  using comparator_t =
      std::conditional_t<std::is_same_v<typename node_t::left_holder, T>,
                         CompareLeft, CompareRight>;

  template <typename T> comparator_t<T> const &get_comparator() const noexcept {
    if constexpr (std::is_same_v<T, typename node_t::left_holder>)
      return left_comparator();
    else if constexpr (std::is_same_v<T, typename node_t::right_holder>)
      return right_comparator();
    else
      return ""; // generate error
  }

  void copy_elements(bimap const &other);

public:
  // it is not me! it is clang format!
  bimap(CompareLeft cl = CompareLeft(),
        CompareRight cr =
            CompareRight()) noexcept(std::
                                         is_nothrow_constructible_v<
                                             left_comparator_holder,
                                             CompareLeft &&>
                                             &&std::is_nothrow_constructible_v<
                                                 right_comparator_holder,
                                                 CompareRight &&>)
      : left_comparator_holder(std::move(cl)),
        right_comparator_holder(std::move(cr)), root(nullptr), sz(0) {}

  bimap(bimap const &other)
      : bimap(other.left_comparator(), other.right_comparator()) {
    copy_elements(other);
  }
  bimap(bimap &&other) noexcept : root(other.root), sz(other.sz) {
    other.root = nullptr;
    other.sz = 0;
  }

  bimap &operator=(bimap const &other) {
    copy_elements(other);
    return *this;
  }
  bimap &operator=(bimap &&other) noexcept {
    std::swap(root, other.root);
    std::swap(sz, other.sz);
    return *this;
  }

  void clear() noexcept {
    if (size() == 0)
      return;
    // iterating over splay tree in increasing order is O(n)
    // Static Finger Theorem
    auto iter = begin_left();
    while (true) {
      auto del = iter;
      ++iter;
      delete del.node;
      if (iter == end_left())
        break;
      assert(iter.node->left_node()->up == nullptr);
      iter.node->left_node()->left = nullptr;
    }
    root = nullptr;
    sz = 0;
  }
  ~bimap() noexcept { clear(); }

private:
  template <typename T> iterator_from_node_type<T> begin_impl() const noexcept {
    using ret_t = iterator_from_node_type<T>;
    if (root == nullptr)
      return ret_t(&root, nullptr);
    auto rt = root->template get_node<T>();
    rt->splay();
    return ret_t(&root, node_t::cast(rt->call(&T::node_t::left_most)));
  }

public:
  left_iterator begin_left() const noexcept {
    return begin_impl<typename node_t::left_holder>();
  }
  left_iterator end_left() const noexcept {
    return left_iterator(&root, nullptr);
  }

  right_iterator begin_right() const noexcept {
    return begin_impl<typename node_t::right_holder>();
  }
  right_iterator end_right() const noexcept {
    return right_iterator(&root, nullptr);
  }

private:
  template <typename T1, typename T2>
  left_iterator insert_impl(T1 &&l, T2 &&r) {
    if (root == nullptr) {
      root = new node_t(std::forward<T1>(l), std::forward<T2>(r));
      sz = 1;
      return left_iterator(&root, root);
    }

    auto fl = root->left_node()->find_ge(l, left_comparator());
    if (fl != nullptr && !left_comparator()(l, fl->data))
      return end_left();
    auto fr = root->right_node()->find_ge(r, right_comparator());
    if (fr != nullptr && !right_comparator()(r, fr->data))
      return end_left();

    auto node = new node_t(std::forward<T1>(l), std::forward<T2>(r));
    // noexcept opertions:

    sz++;

    // My [Left/Right] of Left subtree
    const typename node_t::left_holder::node_t *mll, *mrl;
    if (fl == nullptr) {
      mll = root->left_node()->as_node();
      mrl = nullptr;
    } else {
      auto res = fl->cut();
      mll = res.first;
      mrl = res.second;
    }

    // My [Left/Right] of Right subtree
    const typename node_t::right_holder::node_t *mlr, *mrr;
    if (fr == nullptr) {
      mlr = root->right_node()->as_node();
      mrr = nullptr;
    } else {
      auto res = fr->cut();
      mlr = res.first;
      mrr = res.second;
    }
    node->right_node()->merge(mlr, mrr);
    node->left_node()->merge(mll, mrl);

    root = node;

    return left_iterator(&root, node);
  }

public:
  left_iterator insert(left_t const &a, right_t const &b) {
    return insert_impl(a, b);
  }
  left_iterator insert(left_t const &a, right_t &&b) {
    return insert_impl(a, std::move(b));
  }
  left_iterator insert(left_t &&a, right_t const &b) {
    return insert_impl(std::move(a), b);
  }
  left_iterator insert(left_t &&a, right_t &&b) {
    return insert_impl(std::move(a), std::move(b));
  }

private:
  template <typename holder_t>
  auto erase_impl(bimap_helper::bimap_iterator<node_t, holder_t> it) noexcept
      -> decltype(it) {
    auto ret = it;
    ++ret;

    static_cast<bimap_helper::coholder_t<node_t, holder_t> const *>(it.node)
        ->cutcutmerge();
    root = node_t::cast(static_cast<holder_t const *>(it.node)->call(
        &holder_t::node_t::cutcutmerge));
    sz--;
    delete it.node;
    return ret;
  }

public:
  left_iterator erase_left(left_iterator it) noexcept { return erase_impl(it); }
  right_iterator erase_right(right_iterator it) noexcept {
    return erase_impl(it);
  }

private:
  template <typename T>
  iterator_from_node_type<T> find_impl(typename T::value_type const &wht) const
      noexcept(
          is_nothrow_comparable_v<typename T::value_type, comparator_t<T>>) {
    using ret_t = iterator_from_node_type<T>;
    if (root == nullptr)
      return ret_t(&root, nullptr);
    auto found =
        root->template get_node<T>()->find_ge(wht, get_comparator<T>());
    // found >= wht
    if (found != nullptr && get_comparator<T>()(wht, found->data))
      return ret_t(&root, nullptr);
    return ret_t(&root, node_t::cast(found));
  }

public:
  left_iterator find_left(left_t const &left) const
      noexcept(noexcept(find_impl<typename node_t::left_holder>(left))) {
    return find_impl<typename node_t::left_holder>(left);
  }
  right_iterator find_right(right_t const &right) const
      noexcept(noexcept(find_impl<typename node_t::right_holder>(right))) {
    return find_impl<typename node_t::right_holder>(right);
  }

private:
  template <typename T>
  bool erase_impl(typename T::value_type const &wht) noexcept(
      noexcept(find_impl<T>(wht))) {
    auto found = find_impl<T>(wht);
    // end check
    if (found.node == nullptr)
      return false;
    erase_impl(found);
    return true;
  }

public:
  bool erase_left(left_t const &left) noexcept(
      noexcept(erase_impl<typename node_t::left_holder>(left))) {
    return erase_impl<typename node_t::left_holder>(left);
  }
  bool erase_right(right_t const &right) noexcept(
      noexcept(erase_impl<typename node_t::right_holder>(right))) {
    return erase_impl<typename node_t::right_holder>(right);
  }

private:
  template <typename T> T erase_range(T f, T l) noexcept {
    // optimize?
    // because of dynamic finger theroem it is not so bad as it is
    while (f != l)
      f = erase_impl(f);
    return f;
  }

public:
  left_iterator erase_left(left_iterator f, left_iterator l) noexcept {
    return erase_range(f, l);
  }
  right_iterator erase_right(right_iterator f, right_iterator l) noexcept {
    return erase_range(f, l);
  }

private:
  template <typename T>
  auto const &at_impl(typename T::value_type const &key) const {
    auto iter = find_impl<T>(key);
    // end check
    if (iter.node == nullptr)
      throw std::out_of_range("at_left bad");
    return *iter.flip();
  }

public:
  right_t const &at_left(left_t const &key) const {
    return at_impl<typename node_t::left_holder>(key);
  }
  left_t const &at_right(right_t const &key) const {
    return at_impl<typename node_t::right_holder>(key);
  }

  // this two functions are unmergable b/c of oreder of arguments of insert
  template <typename T, typename = std::enable_if_t<
                            std::is_same_v<T, left_t> &&
                            std::is_default_constructible_v<right_t>>>
  right_t const &at_left_or_default(T const &key) {
    if (auto itl = find_left(key); itl != end_left())
      return *itl.flip();
    // we may search as much as we want for same elements
    // Static Optimality Theorem
    right_t dflt{};
    auto itr = find_right(dflt);
    if (itr != end_right())
      erase_right(itr);
    return *insert(key, std::move(dflt)).flip();
  }
  template <typename T, typename = std::enable_if_t<
                            std::is_same_v<T, right_t> &&
                            std::is_default_constructible_v<left_t>>>
  left_t const &at_right_or_default(T const &key) {
    if (auto itr = find_right(key); itr != end_right())
      return *itr.flip();
    // we may search as much as we want for same elements
    // Static Optimality Theorem
    left_t dflt{};
    auto itr = find_left(dflt);
    if (itr != end_left())
      erase_left(itr);
    return *insert(std::move(dflt), key);
  }

private:
  template <typename T>
  iterator_from_node_type<T>
  lower_bound_impl(typename T::value_type const &key) const noexcept(noexcept(
      root->template get_node<T>()->find_ge(key, get_comparator<T>()))) {
    using ret_t = iterator_from_node_type<T>;
    if (root == nullptr)
      return ret_t(&root, nullptr);
    return ret_t(&root, node_t::cast(root->template get_node<T>()->find_ge(
                            key, get_comparator<T>())));
  }

public:
  left_iterator lower_bound_left(const left_t &left) const
      noexcept(noexcept(lower_bound_impl<typename node_t::left_holder>(left))) {
    return lower_bound_impl<typename node_t::left_holder>(left);
  }
  right_iterator lower_bound_right(const right_t &right) const noexcept(
      noexcept(lower_bound_impl<typename node_t::right_holder>(right))) {
    return lower_bound_impl<typename node_t::right_holder>(right);
  }

private:
  template <typename T>
  iterator_from_node_type<T>
  upper_bound_impl(typename T::value_type const &key) const
      noexcept(noexcept(lower_bound_impl<T>(key))) {
    auto it = lower_bound_impl<T>(key);
    // end check
    if (it.node == nullptr)
      return it;
    // *it >= left
    if (!get_comparator<T>()(key, *it))
      ++it;
    return it;
  }

public:
  left_iterator upper_bound_left(const left_t &left) const
      noexcept(noexcept(lower_bound_left(left))) {
    return upper_bound_impl<typename node_t::left_holder>(left);
  }
  right_iterator upper_bound_right(const right_t &right) const
      noexcept(noexcept(lower_bound_right(right))) {
    return upper_bound_impl<typename node_t::right_holder>(right);
  }

  bool empty() const noexcept { return size() == 0; }
  std::size_t size() const noexcept { return sz; }

  bool operator==(bimap const &b) const {
    auto it1 = begin_left();
    auto it2 = b.begin_left();
    auto const &l = left_comparator();
    auto const &r = right_comparator();
    while (it1 != end_left() && it2 != b.end_left())
      if (bimap_helper::NotEqual(l, *it1, *it2) ||
          bimap_helper::NotEqual(r, *it1.flip(), *it2.flip())) {
        return false;
      } else {
        ++it1;
        ++it2;
      }
    if (it1 != end_left() || it2 != b.end_left())
      return false;
    return true;
  }
  bool operator!=(bimap const &b) const { return !operator==(b); }
};

template <typename Left, typename Right, typename CompareLeft,
          typename CompareRight>
void bimap<Left, Right, CompareLeft, CompareRight>::copy_elements(
    bimap const &other) {
  if (this == &other)
    return;
  clear();
  // iterating over all elements of splay tree is O(n), insert biggest would
  // be O(1) here + rebalance in fututre
  for (auto iter = other.begin_left(); iter != other.end_left(); ++iter)
    insert(*iter, *iter.flip());
}
