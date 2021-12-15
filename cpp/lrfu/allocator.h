#pragma once

#include "pool.h"

#include <cstdint>

class AllocatorWithPool : private PoolAllocator
{
public:
    AllocatorWithPool(const std::size_t size, std::initializer_list<std::size_t> sizes)
        : PoolAllocator(size, sizes)
    { }

    template <class T, class... Args>
    T * create(Args &&... args)
    {
        auto * ptr = allocate(sizeof(T));
        return new (ptr) T(std::forward<Args>(args)...);
    }
    template <typename Type>
    void destroy(Type * ptr)
    {
        ptr->~Type();
        deallocate(ptr);
    }
};
