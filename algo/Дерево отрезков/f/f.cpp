#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdio>
#include <fstream>

using uint = unsigned;

#if !defined(__OPTIMIZE__)
#	include <sstream>
	auto cin = std::stringstream(R"delim(
10 8 12345
3 9
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
	std::vector<type> elements;
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
		elements[i] = w;
		while (i > 0)
		{
			i = (i - 1) / 2;
			elements[i] = descr.oper(elements[2 * i + 1], elements[2 * i + 2]);
		}
	}
	type calc(uint l, uint r, uint x, uint lx, uint rx)
	{
		if (l >= rx || lx >= r)
			return descr.neutral;
		if (lx >= l && rx <= r)
			return elements[x];
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
		elements.resize(2 * n - 1, descr.neutral);
		for (uint i = 0; i < els.size(); i++)
			elements[n - 1 + i] = els[i];
		for (int i = n - 2; i >= 0; i--)
			elements[i] = descr.oper(elements[2 * i + 1], elements[2 * i + 2]);
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
				ansl = descr.oper(ansl, elements[l]);
			l /= 2;
			if (r % 2)
				ansr = descr.oper(elements[r], ansr);
			r = r / 2 - 1;
		}
		if (l == r)
			ansl = descr.oper(ansl, elements[l]);
		return descr.oper(ansl, ansr);
	}
};

template<typename type>
class minimum
{
public:
	type operator()(const type &l, const type &r) { return l < r ? l : r; }
};

class intdescr
{
public:
	using type = int;
	minimum<type> oper;
	const int neutral = 16714588;
};

int main(void)
{
	int n, m;
	cin >> n >> m;
	std::vector<int> els(n);
	cin >> els[0];
	for (int i = 1; i < n; i++)
		els[i] = (23 * els[i - 1] + 21563) % 16714589;
	Tree<intdescr> tree(els);
	int up, vp;
	cin >> up >> vp;
	int res;
	if (up < vp)
		res = tree(up - 1, vp - 1);
	else
		res = tree(vp - 1, up - 1);
	for (int i = 1; i < m; i++)
	{
		up = ((long long)17 * up + 751 + res + 2 * i) % n + 1;
		vp = ((long long)13 * vp + 593 + res + 5 * i) % n + 1;
		if (up < vp)
			res = tree(up - 1, vp);
		else
			res = tree(vp - 1, up);
	}
	std::cout << up << " " << vp << " " << res << std::endl;
	return 0;
}
