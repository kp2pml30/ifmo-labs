#pragma once

#include <vector>
#include <memory>
#include <algorithm>
#include <random>

#include <cstring>
#include <cassert>
#include <ctime>

/* What complexity should it have? Memory/time
 * With impicit key trees it may be log/operation, iteration O(n log n)
 * With array O(1), dequeue O(n), iteration O(n)
 *
 * Should I store shared_ptr even for copyable? or make condition?
 * I guess user must provide wrapping by himself.
 */

template<typename T>
class randomized_queue
{
public:
    using type = T;
private:
    std::vector<type> elements;

    mutable std::mt19937 random_generator = std::mt19937((std::uint_fast32_t)time(nullptr));
    std::size_t get_rand_index(void) const { return std::uniform_int_distribution<std::size_t>(0, elements.size() - 1)(random_generator); }

    template<typename parent_type, typename element_type>
    class iterator_impl
    {
    public:
        using iterator_category = std::bidirectional_iterator_tag;
        using value_type = element_type;
        using difference_type = std::int64_t;
        using pointer = value_type * ;
        using reference = value_type & ;
    private:
        friend randomized_queue;
        // fields
        parent_type *const parent;
        std::size_t position;
        std::shared_ptr<std::size_t[]> indices;

        void make_indices(void)
        {
            const auto max_size = parent->elements.size();
            if (max_size == 0)
                return;
            for (std::size_t i = 0; i < max_size; i++)
                indices[i] = i;
#if 0
            std::random_shuffle(indices.get(), indices.get() + max_size); // deprecated
#else
            for (std::size_t i = 0; i < max_size - 1; i++)
                std::swap(indices[i], indices[std::uniform_int_distribution<std::size_t>(i, max_size - 1)(parent->random_generator)]);
#endif
        }

        explicit iterator_impl(parent_type *parent) : parent(parent), position(parent->elements.size()) {}
        iterator_impl(parent_type *parent, std::size_t position) : parent(parent), position(position), indices(new std::size_t[parent->elements.size()])
        {
            make_indices();
        }

        void decr(void)
        {
            assert(position > 0);
            if (!indices)
            {
                indices = new std::size_t[parent->elements.size()];
                make_indices();
            }
            position--;
        }
    public:
        reference operator*(void) const
        {
            assert(position < parent->size());
            return parent->elements[indices[position]];
        }
        pointer operator->(void) const
        {
            assert(position < parent->size());
            return &parent->elements[indices[position]];
        }

        template<typename parent_type1, typename element_type1>
        bool operator==(const iterator_impl<parent_type1, element_type1> &right) const
        {
            static_assert(std::is_same<std::remove_const<parent_type>, std::remove_const<parent_type1>>::value
                    , "Bad iterator types for comparision");
            return position == right.position && parent == right.parent &&
                   (position == parent->elements.size()
                    || indices == right.indices
                    || memcmp(indices.get(), right.indices.get(), sizeof(std::size_t) * parent->elements.size()) == 0
                   );
        }
        template<typename parent_type1, typename element_type1>
        bool operator!=(const iterator_impl<parent_type1, element_type1> &right) const { return !operator==(right); }

        iterator_impl & operator++(void)
        {
            assert(position < parent->elements.size());
            position++;
            return *this;
        }
        iterator_impl operator++(int)
        {
            assert(position < parent->elements.size());
            iterator_impl before = *this;
            position++;
            return before;
        }
        iterator_impl & operator--(void)
        {
            decr();
            return *this;
        }
        iterator_impl operator--(int)
        {
            iterator_impl before = *this;
            decr();
            return before;
        }
    };
public:
    using iterator = iterator_impl<randomized_queue, T>;
    using const_iterator = iterator_impl<const randomized_queue, const T>;

    iterator begin(void) { return iterator(this, 0); }
    const_iterator begin(void) const { return const_iterator(this, 0); }
    const_iterator cbegin(void) const { return begin(); }

    iterator end(void) { return iterator(this); }
    const_iterator end(void) const { return const_iterator(this); }
    const_iterator cend(void) const { return end(); }

    randomized_queue & enqueue(const T &element) { elements.push_back(element); return *this; }
    randomized_queue & enqueue(T &&element) { elements.push_back(std::move(element)); return *this; }

    std::size_t size(void) const { return elements.size(); }
    bool empty(void) const { return elements.empty(); }

    T & sample(void) { assert(!empty()); return elements[get_rand_index()]; }
    const T & sample(void) const { assert(!empty()); return elements[get_rand_index()]; }
    T dequeue(void)
    {
        assert(!empty());
        std::size_t ind = get_rand_index();
        T ret = std::move(elements[ind]);
        elements.erase(elements.begin() + ind);
        return std::move(ret);
    }
};
