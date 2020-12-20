#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdio>
#include <fstream>

using uint = unsigned;

#if !defined(__OPTIMIZE__)
#	include <sstream>
	auto cin = std::stringstream(R"delim(

)delim");
#else
	using std::cin;
	// std::ifstream cin("crypto.in");
#endif

/*
 * descr class :
 *	type    - typename
 *	oper    - functional class
 *	neutral - static/non-static var of type
 */

template<typename Descr>
class Tree
{
private:
	using type = typename Descr::type;
	Descr descr;
	std::vector<type> els;
	uint n;
	class Setter
	{
	private:
		Tree *parent;
		uint index;
	public:
		Setter(Tree *parent, uint index) : parent(parent), index(index) {}
		void operator=(const type &r)
		{
			return parent->set(index, r);
		}
	};
	void set(uint i, const type &w)
	{
		i += n - 1;
		els[i] = w;
		while (i > 0)
		{
			i = (i - 1) / 2;
			els[i] = descr.oper(els[2 * i + 1], els[2 * i + 2]);
		}
	}
	type calc(uint l, uint r, uint x, uint lx, uint rx)
	{
		if (l >= rx || lx >= r)
			return descr.neutral;
		if (lx >= l && rx <= r)
			return els[x];
		uint m = (lx + rx) / 2;
		return descr.oper(calc(l, r, 2 * x + 1, lx, m), calc(l, r, 2 * x + 2, m, rx));
	}
public:
	Tree(const std::vector<type> &els)
	{
		n = els.size();
		n--;
		n |= n >> 1;
		n |= n >> 2;
		n |= n >> 4;
		n |= n >> 8;
		n |= n >> 16;
		n++;
		els.resize(2 * n - 1, descr.neutral);
		for (uint i = 0; i < els.size(); i++)
			els[n - 1 + i] = els[i];
		for (int i = n - 2; i >= 0; i--)
			els[i] = descr.oper(els[2 * i + 1], els[2 * i + 2]);
	}
	Setter operator[](uint i) { return Setter(this, i); }

	type operator()(uint l, uint r)
	{
		l += n - 1;
		r += n - 2;
		type
			ansl = descr.neutral,
			ansr = descr.neutral;
		while (l < r)
		{
			if (l % 2 == 0)
				ansl = descr.oper(ansl, els[l]);
			l /= 2;
			if (r % 2)
				ansr = descr.oper(els[r], ansr);
			r = r / 2 - 1;
		}
		if (l == r)
			ansl = descr.oper(ansl, els[l]);
		return descr.oper(ansl, ansr);
	}
};

template<typename Descr>
class MassTree
{
private:
	using type = typename Descr::type;
	Descr descr;
	std::vector<type> els, set;
	uint n;
	class Setter
	{
	private:
		MassTree *parent;
		uint index0, index1;
	public:
		Setter(MassTree *parent, uint index0, uint index1) : parent(parent), index0(index0), index1(index1) {}
		void operator=(const type &r)
		{
			return parent->setf(index0, index1, r, 0, 0, parent->n);
		}
	};
	void propagate(uint x, uint lx, uint rx)
	{
		if (rx - lx == 1)
			return;
		if (set[x] == descr.setneutral)
			return;
		set[2 * x + 1] = descr.setoper(set[2 * x + 1], set[x]);
		els[2 * x + 1] = descr.setoper(els[2 * x + 1], set[x]);
		set[2 * x + 2] = descr.setoper(set[2 * x + 2], set[x]);
		els[2 * x + 2] = descr.setoper(els[2 * x + 2], set[x]);
		set[x] = descr.setneutral;
	}
	void setf(uint l, uint r, const type &v, uint x, uint lx, uint rx)
	{
		propagate(x, lx, rx);
		if (l >= rx || lx >= r)
			return;
		if (lx >= l && rx <= r)
		{
			set[x] = descr.setoper(set[x], v);
			els[x] = descr.setoper(els[x], v);
			return;
		}
		auto m = (lx + rx) / 2;
		setf(l, r, v, 2 * x + 1, lx, m );
		setf(l, r, v, 2 * x + 2, m,  rx);
		els[x] = descr.oper(els[2 * x + 1], els[2 * x + 2]);
	}
	type calc(uint l, uint r, uint x, uint lx, uint rx)
	{
		propagate(x, lx, rx);
		if (l >= rx || lx >= r)
			return descr.neutral;
		if (lx >= l && rx <= r)
			return els[x];
		auto m = (lx + rx) / 2;
		return descr.oper(calc(l, r, 2 * x + 1, lx, m), calc(l, r, 2 * x + 2, m, rx));
	}
public:
	MassTree(const std::vector<type> &eless)
	{
		n = eless.size();
		n--;
		n |= n >> 1;
		n |= n >> 2;
		n |= n >> 4;
		n |= n >> 8;
		n |= n >> 16;
		n++;
		set.resize(2 * n - 1, descr.setneutral);
		els.resize(2 * n - 1, descr.neutral);
		for (uint i = 0; i < eless.size(); i++)
			els[n - 1 + i] = eless[i];
		for (int i = n - 2; i >= 0; i--)
			els[i] = descr.oper(els[2 * i + 1], els[2 * i + 2]);
	}
	Setter operator[](std::pair<uint, uint> i) { return Setter(this, i.first, i.second); }

	type operator()(uint l, uint r)
	{
		return calc(l, r, 0 , 0, n);
	}
};

template<typename type>
class minimum
{
public:
	type operator()(const type &l, const type &r) { return l < r ? l : r; }
};

class rmq2
{
public:
	long long set_ = 1LL << 63;
	long long plus_ = 0;
	void combine(void)
	{
		if (set_ == rmq2().set_)
			return;
		set_ += plus_;
		plus_ = 0;
	}
	bool operator==(const rmq2 &r) const { return set_ == r.set_ && plus_ == r.plus_; }
};


class setplusoper
{
public:
	rmq2 operator()(rmq2 l, rmq2 r)
	{
		l.combine();
		r.combine();
		if (l.set_ == rmq2().set_)
			if (r.set_ == rmq2().set_)
				l.plus_ += r.plus_;
			else
				l.set_ = r.set_, l.plus_ = 0;
		else
			if (r.set_ == rmq2().set_)
				l.plus_ += r.plus_;
			else
				l.set_ = r.set_, l.plus_ = 0;
		l.combine();
		return l;
	}
};

bool operator<(rmq2 l, rmq2 r)
{
	if (l == rmq2())
		return false;
	l.combine();
	r.combine();
	if (l.set_ == r.set_ && l.set_ == rmq2().set_)
		return l.plus_ < r.plus_;
	return l.set_ < r.set_;
}

class mindescr
{
public:
	using type = rmq2;
	minimum<type> oper;
	setplusoper setoper;
	const type setneutral = rmq2();
	const type    neutral = rmq2({.set_ = ~rmq2().set_});
};

int main(void)
{
	uint n;
	cin >> n;
	std::vector<rmq2> els(n);
	for (uint i = 0; i < n; i++)
		cin >> els[i].set_;
	MassTree<mindescr> tree(els);
	els.clear();
	els.shrink_to_fit();
	while (!cin.eof())
	{
		std::string str;
		while (!cin.eof() && cin.peek() != '\n')
			str.push_back(cin.get());
		if (cin.eof())
			break;
		cin.get();
		if (str.empty())
			continue;
		uint i, j;
		long long x;
		if (sscanf(str.c_str(), "set %u %u %lld", &i, &j, &x) == 3)
		{
			i--;
			tree[{i, j}] = rmq2({.set_ = x});
		}
		else if (sscanf(str.c_str(), "add %u %u %lld", &i, &j, &x) == 3)
		{
			i--;
			tree[{i, j}] = rmq2({.set_ = rmq2().set_, .plus_ = x});
		}
		else if (sscanf(str.c_str(), "min %u %u", &i, &j) == 2)
		{
			i--;
			rmq2 ans = tree(i, j);
			ans.combine();
			printf("%lld\n", ans.set_);
		}
		else
			return 0;
	}
	return 0;
}
