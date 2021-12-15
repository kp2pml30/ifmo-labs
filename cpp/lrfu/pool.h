#pragma once

#include <cstddef>
#include <initializer_list>
#include <new>
#include <cassert>
#include <algorithm>
#include <list>
#include <cstdint>

class PoolAllocator
{
public:
    PoolAllocator(const std::size_t count, std::initializer_list<std::size_t> sizes)
    {
        assert(sizes.size() > 0);
        std::size_t
            max_size = *std::max_element(sizes.begin(), sizes.end()),
            total_size = count * max_size;
        storage = static_cast<std::uint8_t *>(std::malloc(total_size));
        storage_end = storage + total_size;
    }

    ~PoolAllocator()
    {
        std::free(storage);
    }

    void * allocate(const std::size_t n)
    {
        std::uint8_t *free_start = storage;
        auto it = allocated.begin();
        while (it != allocated.end() && pointers_distance(free_start, it->first) < n)
        {
            free_start = it->first + it->second;
            ++it;
        }
        if (it == allocated.end())
        {
            if (pointers_distance(free_start, storage_end) < n)
                throw std::bad_alloc{};
            allocated.push_back({free_start, n});
            return free_start;
        }
        allocated.insert(it, {free_start, n});
        return free_start;
    }

    void deallocate(const void * ptr)
    {
        if (ptr == nullptr)
            return;
        auto it = allocated.begin();
        while (it != allocated.end())
        {
            if (it->first == ptr)
            {
                allocated.erase(it);
                return;
            }
            else
                ++it;
        }
        throw std::bad_alloc();
    }
private:
    std::uint8_t *storage, *storage_end;
    std::list<std::pair<std::uint8_t *, std::size_t>> allocated; // {start, size_in_bytes}

    std::size_t pointers_distance(std::uint8_t *l, std::uint8_t *r)
    { return static_cast<std::size_t>(r - l); }
};
