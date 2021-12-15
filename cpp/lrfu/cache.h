#pragma once

#include <cstddef>
#include <new>
#include <ostream>
#include <list>
#include <algorithm>
#include <cassert>

template <class Key, class KeyProvider, class Allocator>
class Cache
{
public:
    static_assert(std::has_virtual_destructor_v<KeyProvider>);

    template <class... AllocArgs>
    Cache(const std::size_t cache_size, AllocArgs &&... alloc_args)
        : m_max_top_size(cache_size)
        , m_max_low_size(cache_size)
        , m_alloc(std::forward<AllocArgs>(alloc_args)...)
    { assert(cache_size > 0); }

    ~Cache()
    {
        for (auto &a : privileged)
            m_alloc.template destroy<KeyProvider>(a);
        for (auto &a : unprivileged)
            m_alloc.template destroy<KeyProvider>(a);
    }

    std::size_t size() const
    { return privileged.size() + unprivileged.size(); }

    bool empty() const
    { return size() == 0; }

    template <class T>
    T & get(const Key & key);

    std::ostream & print(std::ostream & strm) const;

    friend std::ostream & operator << (std::ostream & strm, const Cache & cache)
    { return cache.print(strm); }

private:
    const std::size_t m_max_top_size;
    const std::size_t m_max_low_size;
    Allocator m_alloc;

    std::list<KeyProvider *> privileged, unprivileged;

    template <typename T>
    void check_unprivileged_size()
    {
        if (unprivileged.size() >= m_max_low_size)
        {
            m_alloc.template destroy<KeyProvider>(unprivileged.back());
            unprivileged.pop_back();
        }
    }
};

template <class Key, class KeyProvider, class Allocator>
template <class T>
inline T & Cache<Key, KeyProvider, Allocator>::get(const Key & key)
{
    auto finder = [&key](const KeyProvider *p) { return *p == key; };
    auto itp = std::find_if(privileged.begin(), privileged.end(), finder);
    if (itp != privileged.end())
    {
        if (itp != privileged.begin())
            privileged.splice(privileged.begin(), privileged, itp);
    }
    else
    {
        auto itn = std::find_if(unprivileged.begin(), unprivileged.end(), finder);
        if (itn != unprivileged.end())
        {
            privileged.splice(privileged.begin(), unprivileged, itn);
        }
        else
        {
            check_unprivileged_size<T>();
            unprivileged.push_front(m_alloc.template create<T>(key));
            return static_cast<T &>(*unprivileged.front());
        }
        if (privileged.size() > m_max_top_size)
        {
            check_unprivileged_size<T>();
            unprivileged.splice(unprivileged.begin(), privileged, std::prev(privileged.end()));
        }
    }
    return static_cast<T &>(*privileged.front());
}

template <class Key, class KeyProvider, class Allocator>
inline std::ostream & Cache<Key, KeyProvider, Allocator>::print(std::ostream & strm) const
{
    strm << "Priority:";
    for (const auto &a : privileged)
        strm << ' ' << *a;
    strm << "\nRegular:";
    for (const auto &a : unprivileged)
        strm << ' ' << *a;
    return strm << '\n';
}
