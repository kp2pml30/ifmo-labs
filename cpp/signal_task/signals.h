#pragma once
#include <functional>

#include "intrusive_list.h"

namespace signals
{

template <typename T>
struct signal;

template <typename... Args>
struct signal<void (Args...)>
{
    struct connection;
    struct connection_list_tag;
    struct walker_list_tag;
    struct iteration_data;

    struct connection : public intrusive::list_element<connection_list_tag>
    {
    private:
        using super = intrusive::list_element<connection_list_tag>;
        friend signal;

        signal* parent;
        intrusive::list<iteration_data, walker_list_tag> lst;
        std::function<void (Args...)> slot; // noexcept constructible since 2020

        connection(signal* parent, std::function<void (Args...)>&& slot) noexcept
        : parent(parent)
        , slot(std::move(slot))
        {
            parent->lst.push_front(*this);
        }

        void movelinks(connection& r) noexcept
        {
            super::operator=(std::move(static_cast<super&>(r)));
            lst = std::move(r.lst);
            for (auto& a : lst)
                a.held = intrusive::list<connection, connection_list_tag>::to_iterator(*this);
        }
    public:
        connection() = default;
        ~connection()
        {
            disconnect();
        }

        void disconnect() noexcept
        {
            auto next = super::unlink();
            typename intrusive::list<connection, connection_list_tag>::iterator asit;
            if (next != nullptr)
                asit = intrusive::list<connection, connection_list_tag>::to_iterator(*next);
            for (auto& a : lst)
            {
                a.deleted = true;
                a.held = asit;
            }
            if (asit.valid() && asit != parent->lst.end())
                asit->lst.splice(asit->lst.begin(), lst, lst.begin(), lst.end());
            else
                lst.clear();
        }

        connection(connection const&) = delete;
        connection(connection&& r) noexcept : slot(std::move(r.slot))
        {
            movelinks(r);
        }

        connection& operator=(connection const&) = delete;
        connection& operator=(connection&& r) noexcept
        {
            if (this == &r)
                return *this;
            movelinks(r);
            slot = std::move(r.slot);
            return *this;
        }
    };

    struct iteration_data : public intrusive::list_element<walker_list_tag>
    {
        typename intrusive::list<connection, connection_list_tag>::iterator held;
        bool deleted = false;
        explicit iteration_data(decltype(held) held) : held(held)
        {
            held->lst.push_front(*this);
        }
    };

    intrusive::list<connection, connection_list_tag> lst;

    signal() = default;

    signal(signal const&) = delete;
    signal(signal&&) = delete;
    signal& operator=(signal const&) = delete;
    signal& operator=(signal&&) = delete;

    connection connect(std::function<void (Args...)> slot) noexcept
    {
        auto ret = connection(this, std::move(slot));

        return ret;
    }

    void operator()(Args... a)
    {
        if (lst.empty())
            return;
        auto cur = lst.begin();

        while (cur.valid() && cur != lst.end())
        {
            iteration_data d(cur);

            cur->slot(a...);

            if (!d.deleted)
                ++cur;
            else
                cur = d.held;
        }
    }
};

}
