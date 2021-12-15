#pragma once

#include "function-helper.h"

template <typename R, typename... Args>
struct function<R (Args...)>
{
private:
    function_helper::FunctionStorage<R, Args...> storage;
public:
    function() noexcept
    {
        storage.desc = function_helper::EmptyTypeDescriptor<R, Args...>();
    }

    function(function const& other)
    {
        other.storage.desc->Copy(&storage, &other.storage);
    }
    function(function&& other) noexcept
    {
        other.storage.desc->Move(&storage, &other.storage);
    }

    template <typename T>
    function(T val)
    {
        if constexpr (function_helper::is_small_object_v<T>)
            new(&storage.buf) T(std::move(val));
        else
            *reinterpret_cast<const T **>(&storage.buf) = new T(std::move(val));
        storage.desc = function_helper::FunctionTraits<T>::template Descr<R, Args...>();
    }

    function& operator=(function const& rhs)
    {
        if (this == &rhs)
            return *this;
        storage.Copy(rhs.storage);
        return *this;
    }
    function& operator=(function&& rhs) noexcept
    {
        if (this == &rhs)
            return *this;
        storage.desc->Destroy(&storage);
        storage.desc = function_helper::EmptyTypeDescriptor<R, Args...>();
        rhs.storage.desc->Move(&storage, &rhs.storage);
        return *this;
    }

    ~function()
    {
        storage.desc->Destroy(&storage);
    }

    explicit operator bool() const noexcept
    {
        return storage.desc != function_helper::EmptyTypeDescriptor<R, Args...>();
    }

    R operator()(Args... args) const
    {
        return storage.desc->Invoke(&storage, std::forward<Args>(args)...);
    }

    template <typename T>
    T* target() noexcept
    {
        if (function_helper::FunctionTraits<T>::template Descr<R, Args...>() != storage.desc)
            return nullptr;
        if constexpr (function_helper::is_small_object_v<T>)
            return storage.template SmallCast<T>();
        else
            return storage.template BigCast<T>();
    }

    template <typename T>
    T const* target() const noexcept
    {
        if (function_helper::FunctionTraits<T>::template Descr<R, Args...>() != storage.desc)
            return nullptr;
        if constexpr (function_helper::is_small_object_v<T>)
            return storage.template SmallCast<T>();
        else
            return storage.template BigCast<T>();
    }
};
