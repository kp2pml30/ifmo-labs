#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdio>
#include <fstream>
#include <algorithm>

using uint = unsigned;

#if !defined(__OPTIMIZE__)
#	include <sstream>
	auto cin = std::stringstream(R"delim(
4
0 0 2 2
1 1 5 20
-1 3 30 6
5 5 5 5
)delim");
#else
	using std::cin;
#endif

template<typename t1, typename ...t>
auto maxfunc(t1 a, t ...args)
{
	if constexpr (sizeof...(args) == 0)
		return a;
	else
	{
		auto margs = maxfunc(args...);
		return a > margs ? a : margs;
	}
}

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
		uint m = (lx + rx) / 2;

		set[2 * x + 1] = descr.setoper(set[2 * x + 1], set[x]);
		els[2 * x + 1] = descr.setoper(els[2 * x + 1], set[x], lx, m);

		set[2 * x + 2] = descr.setoper(set[2 * x + 2], set[x]);
		els[2 * x + 2] = descr.setoper(els[2 * x + 2], set[x], m, rx);

		els[x] = descr.oper(els[2 * x + 1], els[2 * x + 2]);
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
			els[x] = descr.setoper(els[x], v, lx, rx);
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

class container
{
public:
	int ma = 0, po = 1 << 31;
	container operator+(const container &r) const
	{
		container ret;
		if (ma >= r.ma)
		{
			ret.ma = ma;
			ret.po = po;
		}
		else
		{
			ret.ma = r.ma;
			ret.po = r.po;
		}
		return ret;
	}
	bool operator==(const container &r) const { return ma == r.ma && po == r.po; }
	bool operator!=(const container &r) const { return !operator==(r); }
};

class setplusoper
{
public:
	container operator()(container l, container r)
	{
		container ret;
		ret.ma = l.ma + r.ma;
		ret.po = l.po;
		return ret;
	}
	container operator()(container l, container r, uint lx, uint rx)
	{
		return operator()(l, r);
	}
};

class mindescr
{
public:
	using type = container;
	std::plus<container> oper;
	setplusoper setoper;
	const type setneutral = container();
	const type    neutral = container();
};

struct Query
{
public:
	int x, yl, yg, sum;
};

int main(void)
{
	static constexpr int sizdiv2 = 200005, siz = sizdiv2 * 2;
	uint n;
	cin >> n;
	std::vector<container> initor(siz);
	for (uint i = 0; i < initor.size(); i++)
		initor[i].po = i;
	MassTree<mindescr> tree(initor);
	std::vector<Query> queries;

	for (uint i = 0; i < n; i++)
	{
		int l, t, r, b;
		cin >> l >> t >> r >> b;
		if (b > t)
			std::swap(b, t);
		if (l > r)
			std::swap(l, r);
		l += sizdiv2;
		r += sizdiv2;
		t += sizdiv2;
		b += sizdiv2;
		queries.push_back(Query({l, b, t, +1}));
		queries.push_back(Query({r, b, t, -1}));
	}
	std::sort(queries.begin(), queries.end(), [](Query a, Query b) { return a.x < b.x || a.x == b.x && a.sum > b.sum; });

	int by = 1 << 31, bx = 1 << 31, best = 0;
	for (auto &a : queries)
	{
		tree[{a.yl, a.yg + 1}] = container({a.sum});
		auto cb = tree(0, siz);
		if (cb.ma > best)
		{
			best = cb.ma;
			bx = a.x;
			by = cb.po;
		}
	}

	if (bx == (1 << 31) || by == (1 << 31))
			exit(1);
	std::cout << best << std::endl << bx - sizdiv2 << ' ' << by - sizdiv2 << std::endl;

	return 0;
}
