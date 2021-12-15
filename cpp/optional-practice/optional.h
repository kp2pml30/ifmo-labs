#pragma once

#include <type_traits>
#include <cinttypes>
#include <utility>

constexpr inline struct nullopt_t {} nullopt;
constexpr inline struct in_place_t {} in_place;

namespace optional_helper {
    struct empty_struct {};

    template <typename T, typename U = void>
    union optional_holder_helper;

    template <typename T>
    union optional_holder_helper<T, std::enable_if_t<std::is_trivially_destructible_v<T>>> {
        empty_struct dummy = {};
        T storage;

        constexpr optional_holder_helper() noexcept
        : dummy()
        {}

        template <typename... Args>
        explicit constexpr optional_holder_helper(in_place_t, Args&&... args) noexcept(std::is_nothrow_constructible_v<T, Args&&...>)
        : storage(std::forward<Args>(args)...)
        {}
    };

    template <typename T>
    union optional_holder_helper<T, std::enable_if_t<!std::is_trivially_destructible_v<T>>> {
        empty_struct dummy;
        T storage;

        constexpr optional_holder_helper() noexcept
        : dummy()
        {}

        template <typename... Args>
        explicit constexpr optional_holder_helper(in_place_t, Args&&... args) noexcept(std::is_nothrow_constructible_v<T, Args&&...>)
        : storage(std::forward<Args>(args)...)
        {}

        ~optional_holder_helper()
        {}
    };

    template <typename T>
    class optional_holder {
    protected:
        bool holds;
        optional_holder_helper<T> un;
    public:
        constexpr optional_holder() noexcept
        : holds(false)
        {}
        constexpr optional_holder(nullopt_t) noexcept
        : optional_holder()
        {}

        template <typename... Args>
        explicit constexpr optional_holder(in_place_t, Args&&... args) noexcept(std::is_nothrow_constructible_v<decltype(un), in_place_t, Args&&...>)
        : holds(true)
        , un(in_place, std::forward<Args>(args)...)
        {}

        constexpr optional_holder(T const& t) noexcept(std::is_nothrow_constructible_v<optional_holder_helper<T>, T const&>)
        : optional_holder(in_place, t)
        {}
        constexpr optional_holder(T&& t) noexcept(std::is_nothrow_constructible_v<optional_holder_helper<T>, T&&>)
        : optional_holder(in_place, std::move(t))
        {}
    };

    template <typename T, typename Y = void>
    class optional_destructor;

    template <typename T>
    class optional_destructor<T, std::enable_if_t<std::is_trivially_destructible_v<T>>> : public optional_holder<T> {
    public:
        using optional_holder<T>::optional_holder;

        void reset() noexcept {
            this->holds = false;
        }
    };

    template <typename T>
    class optional_destructor<T, std::enable_if_t<!std::is_trivially_destructible_v<T>>> : public optional_holder<T> {
    public:
        using optional_holder<T>::optional_holder;

        ~optional_destructor() {
            if (this->holds)
                reinterpret_cast<T*>(&this->un.storage)->~T();
        }

        void reset() noexcept {
            if (this->holds) {
                reinterpret_cast<T*>(&this->un.storage)->~T();
                this->holds = false;
            }
        }
    };

    template <typename T, typename Y = void>
    class optional_copy;

    template <typename T>
    class optional_copy<T, std::enable_if_t<std::is_trivially_copyable_v<T>>>
    : public optional_destructor<T> {
    public:
        using optional_destructor<T>::optional_destructor;

        constexpr optional_copy(optional_copy const&) noexcept = default;
        constexpr optional_copy(optional_copy &&) noexcept = default;

        constexpr optional_copy& operator=(optional_copy const&) noexcept = default;
        constexpr optional_copy& operator=(optional_copy&&) noexcept = default;
    };

    template <typename T>
    class optional_copy<T, std::enable_if_t<!std::is_trivially_copyable_v<T>>>
    : public optional_destructor<T> {
    public:
        using optional_destructor<T>::optional_destructor;

        optional_copy(optional_copy const& t) noexcept(noexcept(T(t.un.storage))) {
            this->holds = t.holds;
            if (t.holds)
                new(&this->un.storage) T(t.un.storage);
        }
        optional_copy(optional_copy&& t) noexcept(noexcept(T(std::move(t.un.storage)))) {
            this->holds = t.holds;
            if (t.holds)
                new(&this->un.storage) T(std::move(t.un.storage));
        }

        optional_copy& operator=(optional_copy const& t)
          noexcept(std::is_nothrow_constructible_v<T, T const&> &&
                   std::is_nothrow_assignable_v<T, T const&>) {
            if (!t.holds) {
                this->reset();
                return *this;
            }
            if (this->holds) {
                this->un.storage = t.un.storage;
            } else {
                new(&this->un.storage) T(t.un.storage);
                this->holds = true;
            }
            return *this;
        }
        optional_copy& operator=(optional_copy&& t)
          noexcept(std::is_nothrow_constructible_v<T, T&&> &&
                   std::is_nothrow_assignable_v<T, T&&>) {
            if (!t.holds) {
                this->reset();
                return *this;
            }
            if (this->holds) {
                this->un.storage = std::move(t.un.storage);
            } else {
                new(&this->un.storage) T(std::move(t.un.storage));
                this->holds = true;
            }
            return *this;
        }
    };

    template <typename T>
    using inherit_chain_last = optional_copy<T>;
}

template <typename T>
class optional : public optional_helper::inherit_chain_last<T> {
public:
    using optional_helper::inherit_chain_last<T>::inherit_chain_last;

    constexpr optional(nullopt_t) noexcept
    : optional()
    {}

    optional(optional const&) = default;
    optional(optional&&) = default;

    optional& operator=(optional const&) = default;
    optional& operator=(optional&&) = default;

    optional& operator=(nullopt_t) noexcept {
        this->reset();
        return *this;
    }

    constexpr explicit operator bool() const noexcept {
        return this->holds;
    }

    constexpr T& operator*() noexcept {
        return this->un.storage;
    }
    constexpr T const& operator*() const noexcept {
        return this->un.storage;
    }

    constexpr T* operator->() noexcept {
        return &this->un.storage;
    }
    constexpr T const* operator->() const noexcept {
        return &this->un.storage;
    }

    template <typename... Args>
    void emplace(Args&&... args) noexcept(std::is_nothrow_constructible_v<T, Args&&...>) {
        this->reset();
        new(&this->un.storage) T(std::forward<Args>(args)...);
        this->holds = true;
    }
};

template<typename T>
constexpr bool operator==(optional<T> const &a, optional<T> const &b) noexcept(noexcept(*a == *b)) {
    return static_cast<bool>(a) == static_cast<bool>(b) && (!a || *a == *b);
}

template<typename T>
constexpr bool operator!=(optional<T> const &a, optional<T> const &b) noexcept(noexcept(a == b)) {
    return !(a == b);
}

template<typename T>
constexpr bool operator<(optional<T> const &a, optional<T> const &b) noexcept(noexcept(*a < *b)) {
    return !static_cast<bool>(a) && static_cast<bool>(b) || static_cast<bool>(a) && static_cast<bool>(b) && *a < *b;
}

template<typename T>
constexpr bool operator<=(optional<T> const &a, optional<T> const &b) noexcept(noexcept(a < b) && noexcept(a == b)) {
    return a == b || a < b;
}

template<typename T>
constexpr bool operator>(optional<T> const &a, optional<T> const &b) noexcept(noexcept(a <= b)) {
    return !(a <= b);
}

template<typename T>
constexpr bool operator>=(optional<T> const &a, optional<T> const &b) noexcept(noexcept(a < b)) {
    return !(a < b);
}
