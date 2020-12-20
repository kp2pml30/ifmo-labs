#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdio>
#include <fstream>

using uint = unsigned;

#if !defined(__OPTIMIZE__)
#	include <sstream>
	auto cin = std::stringstream(R"delim(
3 4 4
0 1
0 0

2 1
1 2

0 0
0 2

1 0
0 2

1 4
2 3
1 3
2 2
)delim");
#else
//	using std::cin;
	std::ifstream cin("crypto.in");
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
		return calc(l, r, 0, 0, n);
	}
};

int r = (1U << 31) - 1;

class Mat2x2
{
private:
	int A[2][2] = {};
public:
	Mat2x2(void) {}
	Mat2x2(int a, int b, int c, int d)
	{
		A[0][0] = a % r;
		A[0][1] = b % r;
		A[1][0] = c % r;
		A[1][1] = d % r;
	}

	Mat2x2 & operator=(const Mat2x2 &r) { A[0][0] = r.A[0][0]; A[0][1] = r.A[0][1]; A[1][0] = r.A[1][0]; A[1][1] = r.A[1][1]; return *this; }
	Mat2x2(const Mat2x2 &r) { A[0][0] = r.A[0][0]; A[0][1] = r.A[0][1]; A[1][0] = r.A[1][0]; A[1][1] = r.A[1][1]; }
	Mat2x2(Mat2x2 &&r) { A[0][0] = r.A[0][0]; A[0][1] = r.A[0][1]; A[1][0] = r.A[1][0]; A[1][1] = r.A[1][1]; }

	int * operator[](uint ind) { return A[ind]; }

	Mat2x2 operator*(const Mat2x2 &r) const
	{
		return Mat2x2(
				A[0][0] * r.A[0][0] + A[0][1] * r.A[1][0],
				A[0][0] * r.A[0][1] + A[0][1] * r.A[1][1],
				A[1][0] * r.A[0][0] + A[1][1] * r.A[1][0],
				A[1][0] * r.A[0][1] + A[1][1] * r.A[1][1]
		);
	}
};

class matdescr
{
public:
	using type = Mat2x2;
	std::multiplies<Mat2x2> oper;
	static const Mat2x2 neutral;
};

const Mat2x2 matdescr::neutral = Mat2x2(1, 0, 0, 1);

int main(void)
{
	freopen("crypto.out", "w", stdout);
	uint n, m;
	cin >> r >> n >> m;
	std::vector<Mat2x2> els(n);
	for (uint i = 0; i < n; i++)
	{
		cin >> els[i][0][0];
		cin >> els[i][0][1];
		cin >> els[i][1][0];
		cin >> els[i][1][1];
	}
	Tree<matdescr> tree(els);
	els.clear();
	els.shrink_to_fit();
	for (uint i = 0; i < m; i++)
	{
		uint l, r;
		cin >> l >> r;
		l--;
		auto m = tree(l, r);
		printf("%i %i\n%i %i\n\n", m[0][0], m[0][1], m[1][0], m[1][1]);
	}
	fclose(stdout);
	return 0;
}
