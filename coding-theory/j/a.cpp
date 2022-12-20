#include <cstddef>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <bitset>
#include <limits>
#include <string>
#include <tuple>
#include <utility>
#include <vector>
#include <numeric>
#include <cassert>
#include <map>
#include <algorithm>
#include <sstream>
#include <string_view>
#include <array>
#include <forward_list>
#include <unordered_map>
#include <random>
#include <set>

#define let auto const

#ifdef _DEBUG
constexpr auto IS_DBG = true;

auto cin = std::stringstream(R"delim(
15 19 5
Encode 1 0 1 0 1 0 1
Simulate 0.05 10000 100


)delim");

using std::cout;
#else
constexpr auto IS_DBG = false;

#include <fstream>
//using std::cin;
//using std::cout;
auto cin = std::fstream("input.txt", std::ios_base::in);
auto cout = std::fstream("output.txt", std::ios_base::out);
#endif

#define MAKE_TYPE_S(b) using i##b = std::int##b##_t;
#define MAKE_TYPE_U(b) using u##b = std::uint##b##_t;
#define MAKE_TYPE(b) MAKE_TYPE_S(b) MAKE_TYPE_U(b)

MAKE_TYPE(8) MAKE_TYPE(16) MAKE_TYPE(32) MAKE_TYPE(64)

constexpr auto SHOW_DBG = IS_DBG;

#define DBG if constexpr (SHOW_DBG)
#define REM if constexpr (false)
#define NOP

struct endl_t {} endl;

std::ostream& operator<<(std::ostream& o, endl_t)
{
	o << '\n';
	return o;
}

template<typename T>
class RangeIota {
public:
	struct Iterator
	{
		T data;

		T operator*() const noexcept
		{
			return data;
		}

		bool operator!=(Iterator const& r) const noexcept
		{
			return data != r.data;
		}

		Iterator operator++() noexcept
		{
			data++;
			return *this;
		}

		Iterator operator++(int) noexcept
		{
			return Iterator{++data};
		}
	};
	Iterator begin() const noexcept
	{
		return Iterator{0};
	}

	Iterator end() const noexcept
	{
		return Iterator{e};
	}

	RangeIota(T e) : e(std::move(e)) {}
private:
	const T e;
};

template<class T>
RangeIota(T) -> RangeIota<T>;

/* content */

class Vec {
private:
	using T = std::uint32_t;
	std::vector<T> data;
	static constexpr size_t bits = 32;
	size_t size_ = 0;
public:
	Vec() = default;
	Vec(size_t size) noexcept
	: data((size + bits - 1) / bits, 0)
	, size_(size)
	{}

	Vec(Vec const&) = default;
	Vec(Vec&& r) noexcept
	: data(std::move(r.data))
	, size_(r.size_)
	{
		r.size_ = 0;
	}

	Vec& operator=(Vec const&) = default;
	Vec& operator=(Vec&& r) noexcept
	{
		if (this == &r)
			return *this;
		data = std::move(r.data);
		size_ = r.size_;
		r.size_ = 0;
		return *this;
	}

	size_t size() const noexcept { return size_; }
	bool empty() const noexcept { return size() == 0; }

	void push_back(bool v)
	{
		if (size_ % bits == 0)
			data.push_back(0);
		(*this)[size_++] = v;
	}

	friend Vec operator+(Vec const& l, Vec const& r) noexcept;
	friend Vec operator*(Vec const& l, Vec const& r) noexcept;

	friend Vec& operator+=(Vec& l, Vec const& r) noexcept;
	friend Vec& operator*=(Vec& l, Vec const& r) noexcept;

	friend bool operator==(Vec const& l, Vec const& r) noexcept;
	friend bool operator<(Vec const& l, Vec const& r) noexcept;

	template<typename V>
	struct Accessor {
	private:
		V* v;
		size_t idx;
		friend Vec;
		Accessor(V* v, size_t idx)
		: v(v)
		, idx(idx)
		{
			assert(idx < v->size());
		}
	public:
		operator bool() const noexcept
		{
			return (v->data[idx / bits] & (1 << (idx % bits))) != 0;
		}

		Accessor(Accessor const&) = delete;
		Accessor& operator=(Accessor const&) = delete;

		Accessor& operator=(bool a) noexcept
		{
			auto& byte = v->data[idx / bits];
			auto bit = idx % bits;
			byte = (byte & ~(1 << bit)) | (T(a) << bit);
			return *this;
		}
	};

	Accessor<Vec> operator[](size_t idx) noexcept
	{
		return Accessor<Vec>(this, idx);
	}

	Accessor<const Vec> operator[](size_t idx) const noexcept
	{
		return Accessor<const Vec>(this, idx);
	}

	Accessor<Vec> emplace_back(bool b) noexcept
	{
		let byte = (size_ + bits - 1) / bits;
		if (byte >= data.size())
			data.emplace_back(0);
		size_++;
		(*this)[size_-1] = b;
		return (*this)[size_-1];
	}

	T rest() const noexcept
	{
		let lastByte = size_ / bits;
		let counted = lastByte * bits;
		if (counted >= size_)
			return 0;
		return data[lastByte] & ((1 << (size_ - counted)) - 1);
	}

	bool sum() const noexcept
	{
		auto sum = T(0);
		let lastByte = size_ / bits;
		for (let byte : RangeIota(lastByte))
			sum ^= data[byte];
		sum ^= rest();

		auto ret = false;
		for (let bit : RangeIota(bits))
			ret ^= (sum & (1 << bit)) != 0;

		DBG {
			auto test = false;
			for (let b : *this)
				test ^= b;
			assert(test == ret);
		}

		return ret;
	}

	Vec& shl(size_t s) noexcept
	{
		if (s == 0)
			return *this;
		let full = s / bits;
		data.resize(data.size() + full + 1);
#if 0
		size_ += s;
		if (full != 0)
		{
			data.resize(data.size() + full + 1);
			for (size_t i = data.size() - 1; i >= full; i--)
				data[i] = data[i - full];
			for (size_t i = 0; i < full; i++)
				data[i] = 0;
		}
		s %= bits;
		for (size_t i = data.size(); i > 0; i--)
			data[i] = (data[i] << s) | ((~((1 << (bits - s)) - 1) & data[i - 1]) >> (bits - s));
		data[0] <<= s;
#else
		size_ += s;
		for (size_t i = size_ - 1; i >= s; i--)
			(*this)[i] = !!(*this)[i - s];
		for (size_t i = 0; i < s; i++)
			(*this)[i] = 0;
#endif
		return *this;
	}

	template<typename V>
	class Iterator
	{
	private:
		V* v;
		size_t idx;
		friend Vec;
		Iterator(V* v, size_t idx)
		: v(v)
		, idx(idx)
		{}
	public:
		using iterator_category = std::random_access_iterator_tag;
		using value_type = bool;
		using difference_type = int;
		using pointer = std::nullptr_t;
		using reference = Accessor<V>;

		Iterator() = default;
		Iterator(Iterator const&) = default;
		Iterator(Iterator&&) = default;

		Iterator& operator=(Iterator const&) = default;
		Iterator& operator=(Iterator&&) = default;

		reference operator*() noexcept
		{
			return (*v)[idx];
		}

		Iterator operator++() noexcept
		{
			++idx;
			return *this;
		}

		Iterator operator++(int) noexcept
		{
			auto old = *this;
			++idx;
			return old;
		}

		Iterator operator--() noexcept
		{
			--idx;
			return *this;
		}

		Iterator operator--(int) noexcept
		{
			auto old = *this;
			--idx;
			return old;
		}

		Iterator operator+(int d) noexcept
		{
			return Iterator(v, idx + d);
		}

		Iterator& operator+=(int d) noexcept
		{
			idx += d;
			return *this;
		}

		bool operator==(Iterator const& r) const noexcept
		{
			assert(v == r.v);
			return idx == r.idx;
		}

		bool operator<(Iterator const& r) const noexcept
		{
			assert(v == r.v);
			return idx <= r.idx;
		}

		bool operator!=(Iterator const& r) const noexcept
		{
			return !(*this == r);
		}
	};

	Iterator<Vec> begin() noexcept
	{
		return Iterator<Vec>(this, 0);
	}

	Iterator<Vec> end() noexcept
	{
		return Iterator<Vec>(this, size_);
	}

	Iterator<const Vec> begin() const noexcept
	{
		return Iterator<const Vec>(this, 0);
	}

	Iterator<const Vec> end() const noexcept
	{
		return Iterator<const Vec>(this, size_);
	}
};

void swap(Vec::Accessor<Vec> l, Vec::Accessor<Vec> r)
{
	bool d = r;
	r = (bool)l;
	l = d;
}

Vec operator*(Vec const& l, Vec const& r) noexcept
{
	assert(l.size() == r.size());
	auto ret = Vec(l.size());
	for (size_t i = 0; i < l.data.size(); i++)
		ret.data[i] = l.data[i] & r.data[i];
	return ret;
}

Vec& operator*=(Vec& l, Vec const& r) noexcept
{
	assert(l.size() == r.size());
	auto ret = Vec(l.size());
	for (size_t i = 0; i < l.data.size(); i++)
		l.data[i] &= r.data[i];
	return l;
}

Vec& operator+=(Vec& l, Vec const& r) noexcept
{
	if (l.data.size() < r.data.size())
	{
		l.data.resize(r.data.size(), 0);
		l.size_ = r.size_;
	}
	for (size_t i = 0; i < r.data.size(); i++)
		l.data[i] ^= r.data[i];
	return l;
}

Vec operator+(Vec const& l, Vec const& r) noexcept
{
	auto res = l;
	res += r;
	return res;
}

bool operator==(Vec const& l, Vec const& r) noexcept
{
	if (l.size() != r.size())
		return false;
	let lastByte = l.size_ / Vec::bits;
	for (let byte : RangeIota(lastByte))
		if (l.data[byte] != r.data[byte])
			return false;

	if (l.rest() != r.rest())
		return false;
	return true;
}

bool operator!=(Vec const& l, Vec const& r) noexcept
{
	return !(l == r);
}

bool operator<(Vec const& l, Vec const& r) noexcept
{
	if (l.size() != r.size())
		return l.size() < r.size();
	let lastByte = l.size_ / Vec::bits;
	for (let byte : RangeIota(lastByte))
		if (l.data[byte] != r.data[byte])
			return l.data[byte] < r.data[byte];

	return l.rest() < r.rest();
}

Vec mulPolyGF2(Vec const& l, Vec const& r)
{
	if (l.size() < r .size())
		return mulPolyGF2(r, l);

	auto res = Vec();
	auto l1 = l;
	//size_t shif = 0;
	for (let bit : r)
	{
		if (bit)
		{
			//l1.shl(shif);
			//shif = 0;
			res += l1;
		}
		l1.shl(1);
		//shif += 1;
	}

	return res;
}

template<typename FE, typename FD>
float simulate(size_t n, size_t k, float sigma, size_t iters, size_t maxErrs, FD decode, FE encode)
{
	auto rd = std::random_device();
	auto gen = std::mt19937(rd());
	auto booleans = std::uniform_int_distribution<int>(0, 1);
	auto noiser = std::uniform_real_distribution<float>();

	size_t errs = 0;
	size_t done = 0;

	auto v0 = Vec(k);

	auto vf = Vec(n);

	for (let i : RangeIota(k))
		v0[i] = booleans(gen);
	auto v = encode(v0);
	while (v.size() < n)
		v.push_back(0);

	while (done < iters && errs < maxErrs)
	{
		size_t errsCnt = 0;
		for (let i : RangeIota(n))
			vf[i] = noiser(gen) < sigma ? (errsCnt++, !v[i]) : v[i];

		decode.Decode(vf);
		done++;
		if (vf != v)
		{
			if (errsCnt <= (decode.delta - 1) / 2)
				abort();
			errs++;
		}
	}
	DBG cout << "errs/done " << errs << "/" << done << " sigma=" << sigma << endl;
	return float(errs) / float(done);
}

// c++20 ??
constexpr u64 bit_floor(u64 val)
{
	for (int i = 0; i <= 5; i++)
		val |= val >> (1 << i);
	return val - (val >> 1);
}

static_assert(bit_floor(0) == 0);
static_assert(bit_floor(0) == 0);
static_assert(bit_floor(1) == 1);
static_assert(bit_floor(2) == 2);
static_assert(bit_floor(3) == 2);
static_assert(bit_floor((1ULL << 60) | 0b1011) == (1ULL << 60));

class GF2q
{
public:
	std::vector<u64> logs;
	std::vector<u64> antilogs;

	GF2q(u64 n, u64 primPoly) noexcept
	: logs(n + 1)
	, antilogs(logs.size())
	{
		let maskUp = bit_floor(primPoly);

		logs[0] = 1;
		u64 x = 2;
		for (size_t i = 1; i < logs.size(); i++)
		{
			logs[i] = x;
			x <<= 1;
			if (x & maskUp)
				x ^= primPoly;
		}

		assert(logs[n] == 1);
		DBG {
			for (size_t i = 1; i < logs.size(); i++)
				for (size_t j = i + 1; j < logs.size(); j++)
					assert(logs[i] != logs[j]);
		}
		for (size_t i = 1; i < logs.size(); i++)
			antilogs[logs[i]] = i;
	}

	struct Poly
	{
		std::vector<u64> coefs;
		GF2q* parent;

		size_t size() const noexcept
		{
			return std::max((size_t)1, coefs.size());
		}

		size_t deg() const noexcept
		{
			if (coefs.size() == 0)
				return 0;
			auto deg = coefs.size() - 1;
			while (deg > 0 && coefs[deg] == 0)
				deg--;
			return deg;
		}

		void normalize() noexcept
		{
			while (coefs.size() > 0 && coefs.back() == 0)
				coefs.pop_back();
		}

		Poly& shl(size_t p) noexcept
		{
			if (p == 0)
				return *this;
			coefs.resize(coefs.size() + p);
			for (size_t i = coefs.size() - 1; i >= p; i--)
				coefs[i] = coefs[i - p];
			for (size_t i = 0; i < p; i++)
				coefs[i] = 0;
			return *this;
		}
	};

	u64 mulSafe(u64 l, u64 r) const noexcept
	{
		if (l == 0 || r == 0)
			return 0;
		return logs[(antilogs[l] + antilogs[r]) % (logs.size() - 1)];
	}

	Poly poly(std::initializer_list<u64> p) noexcept
	{
		return Poly{std::move(p), this};
	}
};

GF2q::Poly& operator+=(GF2q::Poly& l, GF2q::Poly const& r) noexcept
{
	if (r.coefs.size() > l.coefs.size())
		l.coefs.resize(r.coefs.size(), 0);
	for (size_t i = 0; i < r.coefs.size(); i++)
		l.coefs[i] ^= r.coefs[i];
	l.normalize();
	return l;
}

GF2q::Poly operator+(GF2q::Poly const& l, GF2q::Poly const& r) noexcept
{
	auto ret = l;
	ret += r;
	return ret;
}

GF2q::Poly& operator*=(GF2q::Poly& l, const u64 r) noexcept
{
	if (r == 0)
	{
		l.coefs.clear();
		return l;
	}
	if (r == 1)
		return l;

	let& antilogs = l.parent->antilogs;
	let& logs = l.parent->logs;
	let ranti = antilogs[r];
	for (auto& c : l.coefs)
		if (c != 0)
			c = logs[(antilogs[c] + ranti) % (logs.size() - 1)];
	l.normalize();
	return l;
}


GF2q::Poly operator*(GF2q::Poly const& l, const u64 r) noexcept
{
	if (r == 0)
		return l.parent->poly({});
	auto res = l;
	res *= r;
	return res;
}

GF2q::Poly operator*(GF2q::Poly const& l, GF2q::Poly const& r) noexcept
{
	if (l.coefs.size() < r.coefs.size())
		return r * l;

	auto res = GF2q::Poly{std::vector<u64>(l.deg() + r.deg() + 1), l.parent};

	auto ml = GF2q::Poly {};
	for (size_t i = 0; i < r.coefs.size(); i++)
	{
		if (r.coefs[i] == 0)
			continue;
		ml = l;
		ml *= r.coefs[i];
		for (size_t c1 = 0; c1 < ml.coefs.size(); c1++)
			res.coefs[i + c1] ^= ml.coefs[c1];
	}

	res.normalize();
	return res;
}

void test_vec_mulpoly()
{
	auto v1 = Vec(4);
	v1[3] = 1;
	v1[1] = 1;
	v1[0] = 1;

	auto v2 = Vec(2);
	v2[0] = 1;
	v2[1] = 1;

	let v3 = mulPolyGF2(v1, v2);
	assert(v3.size() == 5);
	assert(v3[0] == 1);
	assert(v3[1] == 0);
	assert(v3[2] == 1);
	assert(v3[3] == 1);
	assert(v3[4] == 1);

	auto vsh = Vec(1);
	vsh[0] = 1;
	vsh.shl(0);
	assert(vsh[0]);

	vsh.shl(5);
	assert(vsh.size() == 6);
	assert(vsh[5]);
	for (size_t i = 0; i < vsh.size() - 1; i++)
		assert(vsh[i] == 0);

	vsh.shl(65);
	assert(vsh.size() == 6 + 65);
	assert(vsh[5 + 65]);
	for (size_t i = 0; i < vsh.size() - 1; i++)
		assert(vsh[i] == 0);
}

class Decoder
{
public:
	GF2q &field;
	u64 n, b, delta;

	GF2q::Poly S, Lambda, B, T;

	void Decode(Vec& y, bool print = false) noexcept
	{
		S.coefs.clear();
		for (size_t i = b; i <= b + delta - 2; i++)
		{
			auto s_i = u64(0);
			for (size_t bit = 0; bit < y.size(); bit++)
				s_i ^= y[bit] * field.logs[bit * i % n];
			DBG if (print) cout << "S_" << i << " = " << s_i << '\n';
			S.coefs.emplace_back(s_i);
		}

		Lambda.coefs = {1};
		auto m = u64(0);
		auto L = u64(0);
		B.coefs = {1};
		T.coefs.clear();
		for (size_t r = 1; r <= delta - 1; r++)
		{
			if constexpr (!IS_DBG)
			{
				if (r % 2 == 0)
					continue;
			}
			auto Delta_r = u64(0);
			for (size_t j = 0; j <= L; j++)
				Delta_r ^= field.mulSafe(Lambda.coefs[j], S.coefs[r - 1 - j]);
			if (r % 2 == 0)
				assert(Delta_r == 0);
			if (Delta_r == 0)
				continue;
			T = B;
			T.shl(r - m);
			T *= Delta_r;
			T += Lambda;
			if (2 * L <= r - 1)
			{
				B = Lambda;
				B *= field.logs[n - field.antilogs[Delta_r]];
				std::swap(Lambda, T);
				L = r - L;
				m = r;
			}
			else
			{
				std::swap(Lambda, T);
			}
		}
		DBG if (print)
		{
			cout << "Λ(x) = ";
			for (size_t i = 0; i < Lambda.coefs.size(); i++)
			{
				if (Lambda.coefs[i] == 0)
					continue;
				if (i != 0)
					cout << "+ ";
				cout << "a^" << field.antilogs[Lambda.coefs[i]] % n << ' ';
				if (i != 0)
					cout << "x^" << i << " ";
			}
			cout << endl;
		}
		if (L == Lambda.deg())
		{
			assert(Lambda.coefs[0] == 1);
			auto errors = std::vector<size_t> {};
			for (size_t root = 1; root <= n; root++)
			{
				if (errors.size() >= (delta - 1) / 2 || errors.size() == L)
					break;
				auto res = Lambda.coefs[0];
				for (size_t i = 1; i < Lambda.coefs.size(); i++)
					if (Lambda.coefs[i] != 0)
						res ^= field.logs[(field.antilogs[Lambda.coefs[i]] + root * i) % n];
				if (res == 0)
					errors.emplace_back(n - root);
			}

			for (let e : errors)
			{
				DBG if (print) cout << "err " << e << '\n';
				y[e] = !y[e];
			}
		}
	}
};

// returns reminder
Vec divPolyGF2(Vec dividend, Vec const& divisor) {
	assert(dividend.size() != 0);
	for (size_t i = dividend.size() - 1; i + 1 >= divisor.size(); i--)
		if (dividend[i])
		{
			auto cop = divisor;
			cop.shl(i + 1 - divisor.size());
			dividend += cop;
		}
	return dividend;
}

int main()
{
#ifndef _DEBUG
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);
	cout.tie(nullptr);
#endif

	DBG test_vec_mulpoly();

	let b = 1;

	u64 n, mask, delta;
	cin >> n >> mask >> delta;

	auto field = GF2q(n, mask);

	//==== form g(x)
	auto all_cyclo = std::set<u64>();
	for (u64 pow = b; pow <= b + delta - 2; pow++)
	{
		if (all_cyclo.count(pow) > 0)
			continue;
		auto cylotomic_class = std::set<u64>();
		auto cur = pow;
		cylotomic_class.emplace(pow);
		while (true)
		{
			cur = (cur * 2) % n;
			if (cylotomic_class.count(cur) != 0)
				break;
			assert(all_cyclo.count(cur) == 0);
			cylotomic_class.emplace(cur);
		}

		DBG {
			cout << "cyclotomic ";
			for (auto &a : cylotomic_class)
				cout << a << ' ';
			cout << "\n";
		}
		all_cyclo.insert(cylotomic_class.begin(), cylotomic_class.end());
	}

	auto g = field.poly({1});
	//auto muls = std::stringstream {};
	//muls << "a = 1";
	for (auto &a : all_cyclo)
	{
		g = g * field.poly({field.logs[a], 1});
		//muls << " * (a^" << a << " + x)";
	}
	//cout << "///" ;
	//cout << muls.str() << endl;

	g.normalize();

	//cout << 0;
	//for (size_t i = 0; i < g.coefs.size(); i++)
	//	if (g.coefs[i] == 1)
	//		cout << " + x^" << i;
	//cout << std::endl;

	auto g1 = Vec(g.coefs.size());
	for (size_t i = 0; i < g.coefs.size(); i++)
	{
		let c = g.coefs[i];
		assert(c == 0 || c == 1);
		g1[i] = c;
	}

	// TODO
	let k = n - g.deg();

	cout << k << '\n';
	for (let& gi : g.coefs)
		cout << gi << ' ';
	cout << '\n';

	auto encode = [&](Vec const& u) {
		Vec res = u;
		res.shl(g.deg());
		auto rem = divPolyGF2(res, g1);
		for (auto i : RangeIota(g.deg()))
			res[i] = !!rem[i];

		//return mulPolyGF2(u, g1);
		return res;
	};

	//==== iterate commands
	auto dec = Decoder {field, n, b, delta, field.poly({}), field.poly({}), field.poly({}), field.poly({})};
	{
		std::string s;
		std::getline(cin, s);

		while (!cin.eof())
		{
			std::getline(cin, s);
			if (s == "" || s == "\n")
				continue;
			DBG cout << "got line `" << s << "`" << endl;
			auto handle = [&](std::string_view command, auto f) {
				auto view = std::string_view(s);
				if (view.substr(0, command.size()) != command)
					return false;
				auto ss = std::stringstream(s.substr(command.size()));
				f(ss);
				return true;
			};
			auto fail = [](std::string_view err) -> bool {
				throw err;
			};

			false
				|| handle("Encode", [&](std::stringstream& s) {
					// c(x) = u(x)g(x)
					auto u = Vec(k);

					// auto ufld = field.poly({});
					// ufld.coefs.resize(k);

					for (let i : RangeIota(k))
					{
						u64 coef;
						s >> coef;
						assert(coef == 0 || coef == 1);
						u[i] = coef;
						// ufld.coefs[i] = coef;
					}

					auto c = encode(u);
					assert(c.size() <= n);
					for (let b : c)
						cout << b << ' ';
					for (size_t i = c.size(); i < n; i++)
						cout << "0 ";
					cout << '\n';
					/*
						for (let c : (g * ufld).coefs)
							cout << c << ' ';
						cout << "from GFq\n";
					*/
				})
				|| handle("Decode", [&](std::stringstream& s) {

					auto y = Vec(n);
					for (size_t i = 0; i < n; i++)
					{
						int coef;
						s >> coef;
						assert(coef == 0 || coef == 1);
						y[i] = coef;
					}

					dec.Decode(y, true);

					for (let b : y)
						cout << b << ' ';
					cout << '\n';
				})
				|| handle("Simulate ", [&](std::stringstream& s) {
					float db;
					s >> db;
					//let sigma = std::sqrt(0.5 * std::pow(10, -db / 10.0) * n / k);
					size_t iters, maxErrs;
					s >> iters >> maxErrs;
					//if (iters > 100000)
					//	iters /= 2;
					cout << simulate(n, k, db, iters, maxErrs, dec, [&](auto const& u) { return mulPolyGF2(u, g1); });
					cout << endl << std::flush;
				})
				|| handle("//", [&](auto&) {})
				|| fail("unknown command");
		}
	}

	return 0;
}
