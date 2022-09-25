// g++ --std=c++20 1.cpp -o /tmp/1 && /tmp/1

#include <cassert>
#include <map>
#include <list>
#include <type_traits>
#include <string>
#include <iostream>
#include <vector>

template<typename K, typename V>
class LRU
{
private:
	std::size_t limit;
	std::list<std::pair<K const*, V>> order;
	using orderIterator = typename decltype(order)::iterator;
	std::map<K, orderIterator> map;

	void checkInvariants() const
	{
		assert(map.size() <= limit);
		assert(map.size() == order.size());

		// with above proves bijection
		for (auto const& [k, v] : map)
			assert(v->first == &k);
	}

	struct PreconditionData
	{
		std::size_t size;
		std::vector<std::pair<orderIterator, orderIterator>> lastOrder; /// store all pairs of iterators in list (first -> second), i.e. [0 -> 1, 1 -> 2, 2 -> end]
		bool inserted;
		orderIterator focus;
	};

	PreconditionData checkPreconditions()
	{
		decltype(PreconditionData::lastOrder) vec{};
		vec.reserve(order.size() + 1);
		for (auto iter = order.begin(); iter != order.end(); ++iter)
		{
			auto next = std::next(iter);
			vec.emplace_back(iter, next);
		}
		return PreconditionData{order.size(), std::move(vec)};
	}

	void checkPostconditions(PreconditionData const& d)
	{
		if (d.size == limit)
			assert(order.size() == limit);
		else if (d.inserted)
			assert(order.size() == d.size + 1);
		else
			assert(order.size() == d.size);

		assert(d.focus == order.begin());

		assert(d.lastOrder.size() == (d.size == 0 ? 0 : d.size));
		for (std::size_t i = 0; i < d.lastOrder.size(); i++)
		{
			auto const& [l, r] = d.lastOrder[i];
			if (l == d.focus)
			{
				assert(l == order.begin());
			}
			else if (r == d.focus)
			{
				if (d.inserted && d.size == limit)
					assert(i + 2 == d.lastOrder.size()); // that element was the last one and was moved to front
				else
					assert(std::next(l) == d.lastOrder[i + 1].second);
			}
			else
			{
				assert(std::next(l) == r);
			}
		}
	}
public:
	LRU(std::size_t limit) noexcept
		: limit(limit)
	{
		assert(limit > 0);
	}

	template<typename K1>
		requires std::is_same_v<std::remove_cvref_t<K1>, K>
	std::pair<V&, bool> operator[](K1&& key)
	{
		checkInvariants();
#ifndef NDEBUG
		auto precond = checkPreconditions();
#endif

		auto [iter, inserted] = map.emplace(std::forward<K1>(key), orderIterator{});
		auto allocated = inserted;
		if (inserted)
		{
			if (map.size() > limit)
			{
				// limit checked in consturctor => there is prev
				auto back = std::prev(order.end());
				auto found = map.find(*back->first);
				map.erase(found);
				if (limit != 1)
					order.splice(order.begin(), order, back);

				back->first = &iter->first;
				// reconstruct value
				back->second.~V();
				new(&back->second) V{};

				allocated = true;

				iter->second = back;
			}
			else
			{
				order.emplace_front(std::piecewise_construct,
						std::forward_as_tuple(&iter->first),
						std::forward_as_tuple());
				iter->second = order.begin();
			}
		}
		else if (order.size() != 1)
		{
			order.splice(order.begin(), order, iter->second);
		}

		checkInvariants();

#ifndef NDEBUG
		precond.focus = iter->second;
		precond.inserted = inserted;
		checkPostconditions(precond);
#endif
		return {iter->second->second, allocated};
	}

	std::size_t size() const noexcept
	{
		checkInvariants();
		return map.size();
	}
};

// testing
namespace {

struct NoCopy
{
public:
	NoCopy() = default;
	NoCopy(NoCopy&&) = default;
	NoCopy(NoCopy const&) = delete;
};

// problems with cast of first elements...
void assertPairEquals(std::pair<std::string&, bool> l, std::pair<char const*, bool> r)
{
	assert(l.first == r.first);
	assert(l.second == r.second);
}

// to keep single file
void test()
{
	// oneElement
	[]() {
		auto a = LRU<int, std::string>{3};
		assert(a.size() == 0);
		assertPairEquals(a[0], std::make_pair("", true));
		assert(a.size() == 1);
		// no chage after reget
		assertPairEquals(a[0], std::make_pair("", false));
		assert(a.size() == 1);
		a[0].first = "123";
		assert(a.size() == 1);
		assertPairEquals(a[0], std::make_pair("123", false));
		assert(a.size() == 1);
	}();

	// no copies
	[]() {
		auto a = LRU<int, NoCopy>{3};
		a[0];
	}();

	// limit one
	[]() {
		auto a = LRU<int, std::string>{1};
		assert(a.size() == 0);
		assertPairEquals(a[0], std::make_pair("", true));
		assert(a.size() == 1);
		a[0].first = "set";
		assert(a.size() == 1);
		assertPairEquals(a[0], std::make_pair("set", false));
		a[1].first = "set1";
		assert(a.size() == 1);
		assertPairEquals(a[1], std::make_pair("set1", false));
		assertPairEquals(a[0], std::make_pair("", true));
		assertPairEquals(a[0], std::make_pair("", false));
		assertPairEquals(a[1], std::make_pair("", true));
	}();


	// limit two
	[]() {
		auto a = LRU<int, std::string>{2};
		a[0].first = "0";
		a[1].first = "1";
		a[2].first = "2";
		assert(a.size() == 2);
		assertPairEquals(a[2], std::make_pair("2", false));
		assertPairEquals(a[1], std::make_pair("1", false));
		assertPairEquals(a[0], std::make_pair("", true));

		a[0].first = "0";
		a[1].first = "1";
		a[0].first = "0'";
		a[2].first = "2";
		assertPairEquals(a[2], std::make_pair("2", false));
		assertPairEquals(a[0], std::make_pair("0'", false));
		assertPairEquals(a[1], std::make_pair("", true));
		assertPairEquals(a[0], std::make_pair("0'", false));
	}();

#ifdef NDEBUG
	std::cerr << "Please, do not define NDEBUG" << std::endl;
	std::exit(1);
#else
	//assert(false && "this must fail to ensure assertions work");
#endif
}

} // namespace ''

int main()
{
	test();

	return 0;
}
