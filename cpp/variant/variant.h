#include <algorithm>
#include <cassert>
#include <exception>
#include <limits>
#include <tuple>
#include <type_traits>
#include <utility>
#include <new>

template<typename T>
struct in_place_type_t {};
template<typename T>
inline constexpr in_place_type_t<T> in_place_type;

template<std::size_t T>
struct in_place_index_t {};
template<std::size_t T>
inline constexpr in_place_index_t<T> in_place_index;

inline constexpr std::size_t variant_npos = std::numeric_limits<std::size_t>::max();

template<typename ...A>
class variant;

struct bad_variant_access : public std::exception {};

namespace variant_helper
{
	template<std::size_t ind, typename T, typename ...A>
	struct nth_type
	{
		using type = typename nth_type<ind - 1, A...>::type;
	};
	template<typename T, typename ...A>
	struct nth_type<0, T, A...>
	{
		using type = T;
	};
	template<std::size_t ind, typename ...A>
	using nth_type_t = typename nth_type<ind, A...>::type;
}

template<typename Y, typename ...A>
constexpr bool holds_alternative(variant<A...> const& v) noexcept;
template<std::size_t I, typename ...A>
constexpr auto& get(variant<A...>&);
template<typename Y, typename ...A>
constexpr Y& get(variant<A...>&);
template<std::size_t I, typename ...A>
constexpr auto& get(variant<A...> const&);
template<typename Y, typename ...A>
constexpr Y const& get(variant<A...> const&);
template<std::size_t I, typename ...A>
constexpr auto* get_if(variant<A...>*);
template<typename Y, typename ...A>
constexpr Y* get_if(variant<A...>*);
template<std::size_t I, typename ...A>
constexpr auto* get_if(variant<A...> const*);
template<typename Y, typename ...A>
constexpr Y const* get_if(variant<A...> const*);

namespace variant_helper
{
	template<typename A, typename ...T>
	constexpr auto tie_to_tuple(std::tuple<T...>&& t1, A&& r)
	{
		return std::tuple_cat(std::move(t1), std::forward_as_tuple<A>(r));
	}

	template<std::size_t ind, typename Vis, typename Tup, typename T, typename ...A>
	constexpr auto visit_helper(Vis&& vis, Tup&& tup, T&& m, A&& ...tail)
	{
		if (m.valueless_by_exception())
			throw bad_variant_access();
		if (ind == m.index())
		{
			auto next = tie_to_tuple(std::move(tup), get<ind>(std::forward<T>(m)));
			if constexpr (sizeof...(tail) != 0)
				return visit_helper<0>(std::forward<Vis>(vis), std::move(next), std::forward<A>(tail)...);
			else
				return std::apply(std::forward<Vis>(vis), std::move(next));
		}
		else if constexpr (ind + 1 < std::decay_t<decltype(m)>::size())
		{
			return visit_helper<ind + 1>(std::forward<Vis>(vis), std::move(tup), std::forward<T>(m), std::forward<A>(tail)...);
		}
		else
		{
			assert(false);
		}
	}

	template<typename T>
	struct is_bad_tempalte_constructor_spec : std::false_type {};
	template<typename B>
	struct is_bad_tempalte_constructor_spec<in_place_type_t<B>> : std::true_type {};
	template<std::size_t B>
	struct is_bad_tempalte_constructor_spec<in_place_index_t<B>> : std::true_type {};
	template<typename T>
	constexpr bool is_bad_tempalte_constructor_spec_v = is_bad_tempalte_constructor_spec<T>::value;

	template<typename T>
	struct is_variant : std::false_type {};
	template<typename ...A>
	struct is_variant<variant<A...>> : std::true_type {};
	template<typename T>
	constexpr bool is_variant_v = is_variant<T>::value;
	template<typename T>
	using is_dec_variant = is_variant<std::decay_t<T>>;

	template<typename ...A>
	struct constructor_selector;
	template<>
	struct constructor_selector<>
	{
		constexpr static auto get() {}
	};
	template<typename T, typename ...A>
	struct constructor_selector<T, A...> : constructor_selector<A...>
	{
	private:
		using Tarr = T[];
	public:
		using constructor_selector<A...>::get;
		template<typename Y,
			typename = std::void_t<decltype(Tarr{ std::forward<Y>(std::declval<Y&&>()) })>>
		constexpr static auto get(T) { return std::integral_constant<std::size_t, sizeof...(A) + 1>(); }
	};
	template<typename ...A>
	struct constructor_selector<bool, A...> : constructor_selector<A...>
	{
		using constructor_selector<A...>::get;
		template<typename Y,
			typename = std::enable_if_t<std::is_same_v<Y, bool>>>
		constexpr static auto get(bool) { return std::integral_constant<std::size_t, sizeof...(A) + 1>(); }
	};

	template<template<typename> typename F, typename ...A>
	struct all_of_helper;
	template<template<typename> typename F, typename T, typename ...A>
	struct all_of_helper<F, T, A...>
	: std::integral_constant<bool, F<T>::value && all_of_helper<F, A...>::value>
	{};
	template<template<typename> typename F>
	struct all_of_helper<F>
	: std::true_type
	{};

	template<template<typename> typename F, typename ...A>
	static constexpr bool all_of_v = all_of_helper<F, A...>::value;
	template<typename T>
	struct different_types_check
	{
		template<typename Y>
		struct bind
		: std::integral_constant<bool, !std::is_same_v<T, Y>>
		{};
	};

	template<typename T, typename ...A>
	static constexpr bool tail_types_are_different_v = all_of_v<different_types_check<T>::bind, A...>;

	template<typename T, typename ...A>
	static constexpr bool all_types_are_different_v = []() {
		if constexpr (sizeof...(A) == 0)
			return true;
		else
			return all_types_are_different_v<A...> && tail_types_are_different_v<T, A...>;
	}();

	struct variant_empty {};

	template<bool F, typename ...A>
	union variant_holder_union1;
	template<typename ...A>
	using variant_holder_union = variant_holder_union1<all_of_v<std::is_trivially_destructible, A...>, A...>;

	template<bool F>
	union variant_holder_union1<F>
	{};

	template<typename T, typename ...A>
	union variant_holder_union1<true, T, A...>
	{
		T my;
		variant_holder_union<A...> chained;

		template<typename ...R,
			typename = std::enable_if_t<std::is_constructible_v<T, R&&...>>>
		constexpr variant_holder_union1(in_place_index_t<0>, R&& ...a)
		noexcept(noexcept(T(std::forward<R>(a)...)))
		: my(std::forward<R>(a)...)
		{}

		template<std::size_t ind, typename ...R,
			typename = std::enable_if_t<std::is_constructible_v<decltype(chained), in_place_index_t<ind - 1>, R&&...>>>
		constexpr variant_holder_union1(in_place_index_t<ind>, R&& ...a)
		noexcept(noexcept(variant_holder_union<A...>(in_place_index<ind - 1>, std::forward<R>(a)...)))
		: chained(in_place_index<ind - 1>, std::forward<R>(a)...)
		{}

		explicit variant_holder_union1(variant_empty)
		{}

		~variant_holder_union1() = default;
	};
	template<typename T, typename ...A>
	union variant_holder_union1<false, T, A...>
	{
		T my;
		variant_holder_union<A...> chained;

		template<typename ...R,
			typename = std::enable_if_t<std::is_constructible_v<T, R&&...>>>
		constexpr variant_holder_union1(in_place_index_t<0>, R&& ...a)
		noexcept(noexcept(T(std::forward<R>(a)...)))
		: my(std::forward<R>(a)...)
		{}

		template<std::size_t ind, typename ...R,
			typename = std::enable_if_t<std::is_constructible_v<decltype(chained), in_place_index_t<ind - 1>, R&&...>>>
		constexpr variant_holder_union1(in_place_index_t<ind>, R&& ...a)
		noexcept(noexcept(variant_holder_union<A...>(in_place_index<ind - 1>, std::forward<R>(a)...)))
		: chained(in_place_index<ind - 1>, std::forward<R>(a)...)
		{}

		explicit variant_holder_union1(variant_empty)
		{}

		~variant_holder_union1() {}
	};

	template<typename Y, typename T, typename ...A>
	static constexpr std::size_t index_getter = []() -> std::size_t {
		if constexpr (std::is_same_v<Y, T>)
			return 0;
		else if constexpr (sizeof...(A) == 0)
			return variant_npos;
		else
		{
			constexpr std::size_t n = index_getter<Y, A...>;
			if (n == variant_npos)
				return variant_npos;
			return 1 + n;
		}
	}();

	template<typename ...A>
	struct variant_holder_helper;
	template<>
	struct variant_holder_helper<>
	{
		using helped = variant_holder_union<>;

		static constexpr std::size_t size() noexcept
		{
			return 0;
		}
		static void reset(std::size_t ind, helped&) noexcept { assert(ind == 0); }
		static void copy_init(std::size_t, helped&, helped const&) noexcept { assert(false); }
		static void move_init(std::size_t, helped&, helped&) noexcept { assert(false); }
		static void copy_same(std::size_t, helped&, helped const&) noexcept { assert(false); }
		static void move_same(std::size_t, helped&, helped&) noexcept { assert(false); }
		static void swap_same(std::size_t index, helped&, helped&) noexcept { assert(false); }
	};

	template<typename T, typename ...A>
	struct variant_holder_helper<T, A...>
	{
		using helped = variant_holder_union<T, A...>;
		using next_helper = variant_holder_helper<A...>;

		static constexpr std::size_t size() noexcept
		{
			return sizeof...(A) + 1;
		}
		static void reset(std::size_t ind, helped& h) noexcept
		{
			assert(ind <= size());
			if constexpr (all_of_v<std::is_trivially_destructible, T, A...>)
				return;
			else if (ind == size())
				h.my.~T();
			else
				next_helper::reset(ind, h.chained);
		}
		static void copy_init(std::size_t ind, helped& l, helped const& r)
		noexcept(noexcept(next_helper::copy_init(ind, l.chained, r.chained)) && noexcept(T(r.my)))
		{
			assert(ind <= size());
			if (ind == size())
				new(&l.my) T(r.my);
			else
				next_helper::copy_init(ind, l.chained, r.chained);
		}
		static void move_init(std::size_t ind, helped& l, helped& r)
		noexcept(noexcept(next_helper::move_init(ind, l.chained, r.chained)) && noexcept(T(std::move(r.my))))
		{
			assert(ind <= size());
			if (ind == size())
				new(&l.my) T(std::move(r.my));
			else
				next_helper::move_init(ind, l.chained, r.chained);
		}
		// when _index == r._index
		static void copy_same(std::size_t ind, helped& l, helped const& r)
		noexcept(noexcept(next_helper::copy_same(ind, l.chained, r.chained)) && noexcept(l.my = r.my))
		{
			assert(ind <= size());
			if (ind == size())
				l.my = r.my;
			else
				next_helper::copy_same(ind, l.chained, r.chained);
		}
		// when _index == r._index
		static void move_same(std::size_t ind, helped& l, helped& r)
		noexcept(noexcept(next_helper::move_same(ind, l.chained, r.chained)) && noexcept(l.my = std::move(r.my)))
		{
			assert(ind <= size());
			if (ind == size())
				l.my = std::move(r.my);
			else
				next_helper::move_same(ind, l.chained, r.chained);
		}

		template<std::size_t ind, typename ...R>
		static void emplace_ind(helped& l, R&& ...a)
		noexcept(noexcept(nth_type_t<size() - ind, T, A...>(std::forward<R>(a)...)))
		{
			static_assert(ind <= size());
			if constexpr (ind == size())
				new(const_cast<std::remove_const_t<T>*>(&l.my)) T(std::forward<R>(a)...);
			else
				next_helper::template emplace_ind<ind>(l.chained, std::forward<R>(a)...);
		}
		template<std::size_t ind>
		static constexpr auto& get(helped& l) noexcept
		{
			if constexpr (ind == size())
				return l.my;
			else
				return next_helper::template get<ind>(l.chained);
		}
		template<std::size_t ind>
		static constexpr auto const& get(helped const& l) noexcept
		{
			if constexpr (ind == size())
				return l.my;
			else
				return next_helper::template get<ind>(l.chained);
		}

		static void swap_same(std::size_t index, helped& l, helped& r)
		noexcept(all_of_v<std::is_nothrow_swappable, T, A...>)
		{
			using std::swap; // >_<
			if (index == size())
				swap(l.my, r.my);
			else
				next_helper::swap_same(index, l.chained, r.chained);
		}
	};

	template<typename ...A>
	struct variant_holder_indexed
	{
	protected:
		variant_holder_union<A...> data;
		std::size_t _index;

		using helper = variant_holder_helper<A...>;
	public:
		template<std::size_t ind, typename ...R,
			typename = std::enable_if_t<std::is_constructible_v<decltype(data), in_place_index_t<ind>, R&&...>>,
			typename = std::enable_if_t<ind < sizeof...(A)>>
		constexpr variant_holder_indexed(in_place_index_t<ind> i, R&& ...a)
		noexcept(noexcept(variant_holder_union<A...>(i, std::forward<R>(a)...)))
		: data(i, std::forward<R>(a)...)
		, _index(ind)
		{}

		variant_holder_indexed(variant_empty)
		: data(variant_empty())
		, _index(-1)
		{}

		void reset() noexcept
		{
			if (_index == variant_npos)
				return;
			helper::reset(helper::size() - _index, data);
			_index = variant_npos;
		}
	};

	template<bool, typename ...A>
	struct variant_def_constructor1;
	template<typename ...A>
	using variant_def_constructor = variant_def_constructor1<std::is_constructible_v<nth_type_t<0, A...>>, A...>;

	template<typename ...A>
	struct variant_def_constructor1<true, A...>
	: variant_holder_indexed<A...>
	{
		constexpr variant_def_constructor1()
		noexcept(noexcept(variant_holder_indexed<A...>(in_place_index<0>)))
		: variant_holder_indexed<A...>(in_place_index<0>)
		{}

		using variant_holder_indexed<A...>::variant_holder_indexed;

		variant_def_constructor1(variant_def_constructor1 const&) = default;
		variant_def_constructor1(variant_def_constructor1&&) = default;
		variant_def_constructor1& operator=(variant_def_constructor1 const&) = default;
		variant_def_constructor1& operator=(variant_def_constructor1&&) = default;
	};
	template<typename ...A>
	struct variant_def_constructor1<false, A...>
	: variant_holder_indexed<A...>
	{
		constexpr variant_def_constructor1() = delete;

		using variant_holder_indexed<A...>::variant_holder_indexed;

		variant_def_constructor1(variant_def_constructor1 const&) = default;
		variant_def_constructor1(variant_def_constructor1&&) = default;
		variant_def_constructor1& operator=(variant_def_constructor1 const&) = default;
		variant_def_constructor1& operator=(variant_def_constructor1&&) = default;
	};
	
	template<bool F, typename ...A>
	struct variant_destructor1;
	template<typename ...A>
	struct variant_destructor1<true, A...>
	: variant_def_constructor<A...>
	{
		variant_destructor1() = default;
		using variant_def_constructor<A...>::variant_def_constructor;

		~variant_destructor1() = default;

		variant_destructor1(variant_destructor1 const&) = default;
		variant_destructor1(variant_destructor1&&) = default;
		variant_destructor1& operator=(variant_destructor1 const&) = default;
		variant_destructor1& operator=(variant_destructor1&&) = default;
	};
	template<typename ...A>
	struct variant_destructor1<false, A...>
	: variant_def_constructor<A...>
	{
		variant_destructor1() = default;
		using variant_def_constructor<A...>::variant_def_constructor;

		~variant_destructor1()
		{
			this->reset();
		}

		variant_destructor1(variant_destructor1 const&) = default;
		variant_destructor1(variant_destructor1&&) = default;
		variant_destructor1& operator=(variant_destructor1 const&) = default;
		variant_destructor1& operator=(variant_destructor1&&) = default;
	};

	template<typename ...A>
	using variant_destructor = variant_destructor1<all_of_v<std::is_trivially_destructible, A...>, A...>;

	template<bool F, typename ...A>
	struct variant_copy_c1;
	template<typename ...A>
	struct variant_copy_c1<true, A...>
	: variant_destructor<A...>
	{
		variant_copy_c1() = default;
		using variant_destructor<A...>::variant_destructor;

		constexpr variant_copy_c1(variant_copy_c1 const& r) = default;

		variant_copy_c1(variant_copy_c1&& r) = default;
		variant_copy_c1& operator=(variant_copy_c1 const& r) = default;
		variant_copy_c1& operator=(variant_copy_c1&& r) = default;
	};
	template<typename ...A>
	struct variant_copy_c1<false, A...>
	: variant_destructor<A...>
	{
		variant_copy_c1() = default;
		using variant_destructor<A...>::variant_destructor;


		variant_copy_c1(variant_copy_c1 const& r)
		noexcept(noexcept(variant_holder_helper<A...>::copy_init(sizeof...(A) - r._index, this->data, r.data)))
		: variant_destructor<A...>(variant_empty())
		{
			variant_holder_helper<A...>::copy_init(sizeof...(A) - r._index, this->data, r.data);
			this->_index = r._index;
		}

		variant_copy_c1(variant_copy_c1&& r) = default;
		variant_copy_c1& operator=(variant_copy_c1 const& r) = default;
		variant_copy_c1& operator=(variant_copy_c1&& r) = default;
	};

	template<typename ...A>
	using variant_copy_c = variant_copy_c1<
		all_of_v<std::is_trivially_copy_constructible, A...>
			|| !all_of_v<std::is_copy_constructible, A...>,
		A...>;

	template<bool F, typename ...A>
	struct variant_move_c1;
	template<typename ...A>
	struct variant_move_c1<true, A...>
	: variant_copy_c<A...>
	{
		variant_move_c1() = default;
		using variant_copy_c<A...>::variant_copy_c;

		constexpr variant_move_c1(variant_move_c1 const&) = default;

		constexpr variant_move_c1(variant_move_c1&& r) = default;

		variant_move_c1& operator=(variant_move_c1 const& r) = default;
		variant_move_c1& operator=(variant_move_c1&& r) = default;
	};
	template<typename ...A>
	struct variant_move_c1<false, A...>
	: variant_copy_c<A...>
	{
		variant_move_c1() = default;
		using variant_copy_c<A...>::variant_copy_c;

		constexpr variant_move_c1(variant_move_c1 const&) = default;

		variant_move_c1(variant_move_c1&& r)
		noexcept(noexcept(variant_holder_helper<A...>::move_init(variant_holder_helper<A...>::size() - r._index, this->data, r.data)))
		: variant_copy_c<A...>(variant_empty())
		{
			variant_holder_helper<A...>::move_init(variant_holder_helper<A...>::size() - r._index, this->data, r.data);
			this->_index = r._index;
		}

		variant_move_c1& operator=(variant_move_c1 const& r) = default;
		variant_move_c1& operator=(variant_move_c1&& r) = default;
	};

	template<typename ...A>
	using variant_move_c = variant_move_c1<
		all_of_v<std::is_trivially_move_constructible, A...>
			|| !all_of_v<std::is_move_constructible, A...>,
		A...>;

	template<bool F, typename ...A>
	struct variant_copy_a1;
	template<typename ...A>
	struct variant_copy_a1<true, A...>
	: variant_move_c<A...>
	{
		variant_copy_a1() = default;
		using variant_move_c<A...>::variant_move_c;

		constexpr variant_copy_a1(variant_copy_a1 const&) = default;
		constexpr variant_copy_a1(variant_copy_a1&&) = default;

		variant_copy_a1& operator=(variant_copy_a1 const& r) = default;

		variant_copy_a1& operator=(variant_copy_a1&& r) = default;
	};
	template<typename ...A>
	struct variant_copy_a1<false, A...>
	: variant_move_c<A...>
	{
		variant_copy_a1() = default;
		using variant_move_c<A...>::variant_move_c;

		constexpr variant_copy_a1(variant_copy_a1 const&) = default;
		constexpr variant_copy_a1(variant_copy_a1&&) = default;

		variant_copy_a1& operator=(variant_copy_a1 const& r)
		noexcept(noexcept(variant_holder_helper<A...>::copy_same(sizeof...(A) - r._index, this->data, r.data))
			&& noexcept(variant_holder_helper<A...>::copy_init(sizeof...(A) - r._index, this->data, r.data)))
		{
			if (this->_index == r._index)
				variant_holder_helper<A...>::copy_same(sizeof...(A) - r._index, this->data, r.data);
			else
			{
				this->reset();
				variant_holder_helper<A...>::copy_init(sizeof...(A) - r._index, this->data, r.data);
				this->_index = r._index;
			}
			return *this;
		}

		variant_copy_a1& operator=(variant_copy_a1&& r) = default;
	};

	template<typename ...A>
	using variant_copy_a = variant_copy_a1<
		(all_of_v<std::is_trivially_copy_assignable, A...>
				&& all_of_v<std::is_trivially_copy_constructible, A...>)
			|| !all_of_v<std::is_copy_assignable, A...>
			|| !all_of_v<std::is_copy_constructible, A...>,
		A...>;

	template<bool F, typename ...A>
	struct variant_move_a1;
	template<typename ...A>
	struct variant_move_a1<true, A...>
	: variant_copy_a<A...>
	{
		variant_move_a1() = default;
		using variant_copy_a<A...>::variant_copy_a;

		constexpr variant_move_a1(variant_move_a1 const&) = default;
		constexpr variant_move_a1(variant_move_a1&&) = default;
		variant_move_a1& operator=(variant_move_a1 const& r) = default;

		variant_move_a1& operator=(variant_move_a1&& r) = default;
	};
	template<typename ...A>
	struct variant_move_a1<false, A...>
	: variant_copy_a<A...>
	{
		variant_move_a1() = default;
		using variant_copy_a<A...>::variant_copy_a;

		constexpr variant_move_a1(variant_move_a1 const&) = default;
		constexpr variant_move_a1(variant_move_a1&&) = default;
		variant_move_a1& operator=(variant_move_a1 const& r) = default;

		variant_move_a1& operator=(variant_move_a1&& r)
		noexcept(noexcept(variant_holder_helper<A...>::move_same(sizeof...(A) - r._index, this->data, r.data))
			&& noexcept(variant_holder_helper<A...>::move_init(sizeof...(A) - r._index, this->data, r.data)))
		{
			using helper = variant_holder_helper<A...>;
			if (this->_index == r._index)
				helper::move_same(helper::size() - r._index, this->data, r.data);
			else
			{
				this->reset();
				helper::move_init(helper::size() - r._index, this->data, r.data);
				this->_index = r._index;
			}
			return *this;
		}
	};

	template<typename ...A>
	using variant_move_a = variant_move_a1<
		(all_of_v<std::is_trivially_move_assignable, A...>
				&& all_of_v<std::is_trivially_move_constructible, A...>)
			|| !all_of_v<std::is_move_assignable, A...>
			|| !all_of_v<std::is_move_constructible, A...>,
		A...>;
}

template<typename ...A>
class variant : private variant_helper::variant_move_a<A...>
{
private:
	using helper = variant_helper::variant_holder_helper<A...>;
public:
	static_assert(sizeof...(A) > 0);

	variant() = default;
	using variant_helper::variant_move_a<A...>::variant_move_a;

	~variant() = default;

	constexpr static std::size_t size() noexcept
	{
		return sizeof...(A);
	}

	template<std::size_t ind, typename ...R, typename = std::enable_if_t<ind < size()>>
	void emplace(R&& ...a)
	noexcept(noexcept(helper::template emplace_ind<size() - ind, R...>(this->data, std::forward<R>(a)...)))
	{
		this->reset();
		helper::template emplace_ind<size() - ind, R...>(this->data, std::forward<R>(a)...);
		this->_index = ind;
	}
	template<typename Y, typename ...R,
		std::size_t ind = variant_helper::index_getter<Y, A...>,
		typename = std::enable_if_t<ind != variant_npos>>
	void emplace(R&& ...a)
	noexcept(noexcept(emplace<ind>(std::forward<R>(a)...)))
	{
		emplace<ind>(std::forward<R>(a)...);
	}

	constexpr variant(variant const&) = default;
	constexpr variant(variant&&) = default;
	variant& operator=(variant const& r) = default;
	variant& operator=(variant&& r) = default;

	template<typename Y, typename ...R,
		std::size_t ind = variant_helper::index_getter<Y, A...>,
		typename = std::enable_if_t<ind != variant_npos>,
		typename = std::enable_if_t<std::is_constructible_v<Y, R&&...>>>
	constexpr variant(in_place_type_t<Y>, R&& ...a)
	noexcept(noexcept(variant(in_place_index<ind>, std::forward<R>(a)...)))
	: variant(in_place_index<ind>, std::forward<R>(a)...)
	{}

	template<typename Y,
		typename = std::enable_if_t<!std::is_same_v<std::decay_t<Y>, variant>>,
		std::size_t ind = decltype(variant_helper::constructor_selector<A...>::template get<Y>(std::declval<Y>()))::value,
		typename = std::enable_if_t<ind <= size()>,
		typename = std::enable_if_t<!variant_helper::is_bad_tempalte_constructor_spec_v<std::decay_t<Y>>>,
		typename = std::enable_if_t<std::is_constructible_v<variant, in_place_index_t<size() - ind>, Y&&>>>
	constexpr variant(Y&& y)
	noexcept(noexcept(variant(in_place_index<size() - ind>, std::forward<Y>(y))))
	: variant(
		in_place_index<size() - ind>,
		std::forward<Y>(y))
	{}

	template<typename Y,
		typename = std::enable_if_t<!std::is_same_v<std::remove_const_t<std::remove_reference_t<Y>>, variant>>,
		std::size_t ind = decltype(variant_helper::constructor_selector<A...>::template get<Y>(std::declval<Y>()))::value,
		typename = std::enable_if_t<ind <= size()>,
		typename = std::enable_if_t<!variant_helper::is_bad_tempalte_constructor_spec_v<std::decay_t<Y>>>>
	variant& operator=(Y&& y)
	noexcept(noexcept(std::is_nothrow_assignable_v<variant_helper::nth_type<size() - ind, A...>&, Y&&>)
		&& noexcept(emplace<size() - ind>(std::forward<Y>(y))))
	{
		constexpr std::size_t shifted_ind = size() - ind;
		using Tj = variant_helper::nth_type_t<shifted_ind, A...>;
		if (shifted_ind == index())
		{
			visit([&y](auto& self) {
					if constexpr (std::is_same_v<std::decay_t<decltype(self)>, Tj>)
						self = std::forward<Y>(y);
				},
				*this);
		}
		else if constexpr (std::is_nothrow_constructible_v<Tj, Y&&>
				|| !std::is_nothrow_move_constructible_v<Tj>)
		{
			emplace<shifted_ind>(std::forward<Y>(y));
		}
		else
		{
			*this = variant(std::forward<Y>(y));
		}
		return *this;
	}

	constexpr bool valueless_by_exception() const noexcept
	{
		return this->_index == variant_npos;
	}

	constexpr auto index() const noexcept
	{
		return this->_index;
	}

	void swap(variant& r)
	noexcept(noexcept(helper::swap_same(size() - index(), this->data, r.data))
		&& std::is_nothrow_move_assignable_v<variant>)
	{
		if (valueless_by_exception())
			if (r.valueless_by_exception())
			{
				return;
			}
			else
			{
				*this = std::move(r);
				r.reset();
			}
		else if (r.valueless_by_exception())
		{
			r = std::move(*this);
			this->reset();
		}
		else if (index() == r.index())
		{
			helper::swap_same(size() - index(), this->data, r.data);
		}
		else
		{
			variant tmp = std::move(*this);
			*this = std::move(r);
			r = std::move(tmp);
		}
	}

	template<typename Y>
	friend constexpr bool holds_alternative(variant const& v) noexcept
	{
		if (v.valueless_by_exception())
			return false;
		return v._index == variant_helper::index_getter<Y, A...>;
	}
	template<std::size_t I>
	friend constexpr auto& get(variant& v)
	{
		if (v.valueless_by_exception() || v.index() != I)
			throw bad_variant_access();
		return helper::template get<size() - I>(v.data);
	}
	template<typename Y>
	friend constexpr Y& get(variant& v)
	{
		constexpr std::size_t ind = variant_helper::index_getter<Y, A...>;
		return get<ind>(v);
	}
	template<std::size_t I>
	friend constexpr auto const& get(variant const& v)
	{
		if (v.valueless_by_exception() || v._index != I)
			throw bad_variant_access();
		return helper::template get<I>(v.data);
	}
	template<typename Y,
		std::size_t ind = variant_helper::index_getter<Y, A...>,
		typename = std::enable_if_t<ind <= size()>>
	friend constexpr Y const& get(variant const& v)
	{
		return get<helper::size() - ind>(v);
	}
	template<std::size_t I>
	friend constexpr variant_helper::nth_type_t<I, A...>* get_if(variant* v) noexcept
	{
		if (v == nullptr)
			return nullptr;
		if (v->valueless_by_exception() || v->index() != I)
			return nullptr;
		return &helper::template get<size() - I>(v->data);
	}
	template<std::size_t I>
	friend constexpr variant_helper::nth_type_t<I, A...> const* get_if(variant const* v) noexcept
	{
		if (v == nullptr)
			return nullptr;
		if (v->valueless_by_exception() || v->index() != I)
			return nullptr;
		return &helper::template get<size() - I>(v->data);
	}
	template<typename Y>
	friend constexpr Y* get_if(variant* v) noexcept
	{
		constexpr std::size_t ind = variant_helper::index_getter<Y, A...>;
		static_assert(ind < sizeof...(A));
		return get_if<ind>(v);
	}
	template<typename Y>
	friend constexpr Y const* get_if(variant const* v) noexcept
	{
		constexpr std::size_t ind = variant_helper::index_getter<Y, A...>;
		static_assert(ind < sizeof...(A));
		return get_if<ind>(v);
	}
};

template<typename V, typename ...Vars,
	typename = std::enable_if_t<variant_helper::all_of_v<variant_helper::is_dec_variant, Vars...>>>
constexpr auto visit(V&& v, Vars&& ...a)
{
	if constexpr (sizeof...(Vars) == 0)
		return v();
	else
		return variant_helper::visit_helper<0>(std::forward<V>(v), std::tuple<>(), std::forward<Vars>(a)...);
}

template<typename V>
using variant_size = std::integral_constant<std::size_t, V::size()>;
template<typename V>
inline constexpr std::size_t variant_size_v = variant_size<V>::value;

template<std::size_t ind, typename V>
struct variant_alternative;
template<std::size_t ind, typename ...A>
struct variant_alternative<ind, variant<A...>>
{
	static_assert(ind < sizeof...(A));
	using type = variant_helper::nth_type_t<ind, A...>;
};
template<std::size_t ind, typename ...A>
struct variant_alternative<ind, const variant<A...>>
{
	static_assert(ind < sizeof...(A));
	using type = const variant_helper::nth_type_t<ind, A...>;
};
template<std::size_t ind, typename V>
using variant_alternative_t = typename variant_alternative<ind, V>::type;

