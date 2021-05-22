#include <cassert>
#include <array>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <map>
#include <functional>
#include <set>
#include <unordered_set>
#include <list>
#include <memory>
#include <deque>
#include <queue>
#include <variant>
#include <numeric>
#include <optional>
#include <chrono>
#include <complex>
/// #include <numbers> thnx codeforces

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
2
1 4 2
2 5 6

)delim");
using std::cout;
#else
using std::cin;
using std::cout;
// static auto cin = std::ifstream("matching.in");
// static auto cout = std::ofstream("matching.out");
#endif

// #define EOLYMP

using uint = std::uint32_t;
using size_type = std::int64_t;
using cost_t = std::int64_t;
using flow_t = std::int32_t;

constexpr flow_t infflow = 1'000'000'000;

template<typename T>
struct CollectionAllocator
{
private:
	static std::vector<T> cols;
public:

	static T Get()
	{
		if (!cols.empty())
		{
			auto r = std::move(cols.back());
			cols.pop_back();
			return r;
		}
		return T{};
	}

	static void Retract(T&& c)
	{
		c.clear();
		cols.push_back(std::move(c));
	}

	struct Returner
	{
		void operator()(T* t) noexcept
		{
			Retract(std::move(*t));
		}
	};
	using Flush = std::unique_ptr<T, Returner>;
};
template<typename T>
std::vector<T> CollectionAllocator<T>::cols;

#pragma once

#include <utility>
#include <exception>

#define METOPT_DEF_CONCAT_IMPL(s1, s2) s1 ## s2
#define METOPT_DEF_CONCAT(s1, s2) METOPT_DEF_CONCAT_IMPL(s1, s2)

#define METOPT_UNIQUE_NAME(pref) METOPT_DEF_CONCAT(pref, __LINE__)

namespace impl
{
	template<typename Func, typename CRTP>
	struct ConditionalScopeGuard
	{
	private:
		Func func;
	public:
		ConditionalScopeGuard(Func func)
			: func(std::move(func))
		{}

		~ConditionalScopeGuard() noexcept(noexcept(func()))
		{
			if (static_cast<CRTP&>(*this).NeedsRun())
				func();
		}
	};
	template<template<typename> typename Nested>
	struct ScopeGuardWorkaround
	{
		template<typename Func>
		Nested<Func> operator+(Func&& f)
		{
			return Nested<std::decay_t<Func>>{std::forward<Func>(f)};
		}
	};

	template<typename Func>
	struct ScopeGuard : ConditionalScopeGuard<Func, ScopeGuard<Func>>
	{
	private:
		using Base = ConditionalScopeGuard<Func, ScopeGuard<Func>>;

	public:
		using Base::Base;
		bool NeedsRun() noexcept { return true; }
	};


	template<typename Func, bool succ>
	struct ScopeGuardExcept : ConditionalScopeGuard<Func, ScopeGuardExcept<Func, succ>>
	{
	private:
		using Base = ConditionalScopeGuard<Func, ScopeGuardExcept<Func, succ>>;
		int initialExceptions;

	public:
		ScopeGuardExcept(Func&& f)
			: Base(std::forward<Func>(f))
			, initialExceptions(std::uncaught_exceptions())
		{}

		bool NeedsRun() noexcept
		{
			return (std::uncaught_exceptions() == initialExceptions) == succ;
		}
	};

	template<typename Func>
	using ScopeGuardSucc = ScopeGuardExcept<Func, true>;
	template<typename Func>
	using ScopeGuardFail = ScopeGuardExcept<Func, false>;
}

#define SCOPE_GUARD_IMPL(x) auto METOPT_UNIQUE_NAME(guard_) = impl::ScopeGuardWorkaround<x>{} + [&]() noexcept

#define SCOPE_GUARD_EX auto METOPT_UNIQUE_NAME(guard_) = impl::ScopeGuardWorkaround<impl::ScopeGuard>{} +
#define SCOPE_GUARD SCOPE_GUARD_IMPL(impl::ScopeGuard)
#define SCOPE_SUCCESS SCOPE_GUARD_IMPL(impl::ScopeGuardSucc)
#define SCOPE_FAIL SCOPE_GUARD_IMPL(impl::ScopeGuardFail)

using cmplx = std::complex<double>;

template<bool inverted = false>
void fft_inplace(std::vector<cmplx>& a)
{
	int n = static_cast<int>(a.size());
	if (n == 1)
		return;

	using alloc = CollectionAllocator< std::vector<cmplx>>;

	auto a0 = alloc::Get();
	a0.resize(n / 2);
	SCOPE_GUARD{ alloc::Retract(std::move(a0)); };
	auto a1 = alloc::Get();
	a1.resize(n / 2);
	SCOPE_GUARD{ alloc::Retract(std::move(a1)); };

	for (int j = 0; j * 2 < n; j++)
	{
		a0[j] = a[j * 2 + 0];
		a1[j] = a[j * 2 + 1];
	}
	fft_inplace<inverted>(a0);
	fft_inplace<inverted>(a1);

	const auto omega = 2 * 3.1415926535897932384626433832795 / n * (inverted ? -1 : 1);
	cmplx w = 1;
	const auto wn = cmplx { cos(omega), sin(omega) };
	for (int i = 0; i < n / 2; i++)
	{
		a[i] = a0[i] + w * a1[i];
		a[i + n / 2] = a0[i] - w * a1[i];
		if constexpr (inverted)
		{
			a[i] /= 2;
			a[i + n / 2] /= 2;
		}
		w *= wn;
	}
}

template<typename Int>
Int roundPow2(Int a)
{
	Int r = 1;
	while (r < a)
		r *= 2;
	return r;
}

std::vector<int> mulpoly(std::vector<int> const& a, std::vector<int> const& b)
{
	auto fa = std::vector<cmplx>(a.begin(), a.end());
	auto fb = std::vector<cmplx>(b.begin(), b.end());
	const auto n = 2 * roundPow2((int)std::max(a.size(), b.size()));
	fa.resize(n, {});
	fb.resize(n, {});

	fft_inplace(fa);
	fft_inplace(fb);
	for (size_t i = 0; i < n; ++i)
		fa[i] *= fb[i];
	fft_inplace<true>(fa);

	auto res = std::vector<int>(n);
	for (size_t i = 0; i < n; ++i)
		res[i] = std::round(fa[i].real());
	return res;
}

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	int n;

	cin >> n;

	auto a = std::vector<int>(n + 1);
	auto b = std::vector<int>(n + 1);

	for (int i = 0; i < n + 1; i++)
		cin >> a[i];
	for (int i = 0; i < n + 1; i++)
		cin >> b[i];

	auto res = mulpoly(a, b);
	res.resize(2 * n + 1);
	for (auto const& i : res)
		cout << i << " ";

	cout << std::endl;

	return 0;
}