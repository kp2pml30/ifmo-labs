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
3 1
1 2 1
1 1 2
)delim");
	using std::cout;
#else
	// using std::cin;
	std::ifstream cin("rmq.in");
	std::ofstream cout("rmq.out");
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
	void siftdown(uint x, uint lx, uint rx)
	{
		if (lx - rx <= 1 || x >= els.size())
			return;
		propagate(x, lx, rx);
		auto m = (lx + rx) / 2;
		siftdown(2 * x + 1, lx, m);
		siftdown(2 * x + 2, m, rx);
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
		RecalcFromLeaves();
	}
	Setter operator[](std::pair<uint, uint> i) { return Setter(this, i.first, i.second); }

	type operator()(uint l, uint r)
	{
		return calc(l, r, 0 , 0, n);
	}

	void RecalcFromLeaves(void)
	{
		for (int i = n - 2; i >= 0; i--)
			els[i] = descr.oper(els[2 * i + 1], els[2 * i + 2]);
	}

	type * data(void)
	{
		siftdown(0, 0, n);
		return els.data() + n - 1;
	}
};

template<typename type>
class minimum
{
public:
	type operator()(const type &l, const type &r)
	{
		if (l.val == 1LL << 63)
			return r;
		if (r.val == 1LL << 63)
			return l;
		return l < r ? l : r;
	}
};

class setter
{
public:
	long long val;
	setter(void) : val(1LL << 63) {}
	setter(long long val) : val(val) {}
	bool operator<(const setter &r) const { return val < r.val; }
	setter & operator=(const setter &r) { val = r.val; return *this; }
	bool operator==(const setter &r) { return val == r.val; }
	bool operator!=(const setter &r) { return val != r.val; }
};

class SetOper
{
public:
	setter operator()(setter l, setter r)
	{
		if (l == (1LL << 63))
			return r;
		return l;
	}
};

class mindescr
{
public:
	using type = setter;
	minimum<type> oper;
	SetOper setoper;
	const type setneutral = 1LL << 63;
	const type    neutral = 1LL << 63;
};

class query
{
public:
	uint i, j;
	long long q;
	bool operator<(const query &r) const
	{
		return q > r.q;
	}
};

int main(void)
{
	uint n, m;
	cin >> n >> m;
	std::vector<setter> els(n);
	std::vector<query> queries(m);
	MassTree<mindescr> tree(els);
	els.clear();
	els.shrink_to_fit();


	for (uint _ = 0; _ < m; _++)
	{
		cin >> queries[_].i >> queries[_].j >> queries[_].q;
		queries[_].i--;
	}
	std::sort(queries.begin(), queries.end());
	for (auto &que : queries)
		tree[{que.i, que.j}] = que.q;
	auto data = tree.data();
	tree.RecalcFromLeaves();
	bool bad = false;
	for (auto &que : queries)
	{
		// std::cout << que.i << " " << que.j << " => " << tree(que.i, que.j).val << " " << que.q << std::endl;
		if (tree(que.i, que.j) != que.q)
		{
			bad = true;
			break;
		}
	}
	/*
	for (uint i = 0; i < n; i++)
		if (data[i].val == (1LL << 63))
		{
			bad = true;
			break;
		}
	*/
	if (bad)
	{
		cout << "inconsistent" << std::endl;
		return 0;
	}
	cout << "consistent" << std::endl;
	for (uint i = 0; i < n; i++)
	{
		long long val = data[i].val;
		if (val == (1LL << 63))
			val = 0;
		cout << val << " ";
	}
	cout << std::endl;
	return 0;
}
