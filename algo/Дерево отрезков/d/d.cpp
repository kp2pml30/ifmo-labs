#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdio>
#include <fstream>

using uint = unsigned;

#if !defined(__OPTIMIZE__)
#	include <sstream>
	auto cin = std::stringstream(R"delim(
7
W 2 3
B 2 2
B 4 2
B 3 2
B 7 2
W 3 1
W 0 10
)delim");
#else
	using std::cin;
	// std::ifstream cin("crypto.in");
#endif

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
	uint sum, count = 0;
	bool hasl, hasr;
	container(uint sum = 0, uint count = 0, bool hasl = 1, bool hasr = 1) : sum(sum), count(count), hasl(hasl), hasr(hasr) {}
	container operator+(const container &r) const
	{
		if (sum == (uint)-1)
			return r;
		if (r.sum == (uint)-1)
			return *this;
		// sums are not zero
		container ret;
		ret.sum = sum + r.sum;
		ret.hasl = hasl;
		ret.hasr = r.hasr;
		ret.count = count + r.count - hasr * r.hasl;
		return ret;
	}
	bool operator==(const container &r) const { return sum == r.sum; }
	bool operator!=(const container &r) const { return !operator==(r); }
};

class setplusoper
{
public:
	container operator()(container l, container r)
	{
		if (r.sum == (uint)-1)
			return l;
		return r;
	}
	container operator()(container l, container r, uint lx, uint rx)
	{
		if (r.sum == (uint)-1)
			return l;
		if (l.sum == (uint)-1)
			return r;
		auto ans = container(r.sum * (rx - lx), r.sum);
		ans.hasl = ans.hasr = !!r.sum;
		return ans;
	}
};

class mindescr
{
public:
	using type = container;
	std::plus<container> oper;
	setplusoper setoper;
	const type setneutral = container(-1);
	const type    neutral = container(0, 0, 0, 0);
};

int main(void)
{
	uint m;
	cin >> m;
	container initor(0, 0);
	initor.hasl = initor.hasr = false;
	MassTree<mindescr> tree(std::vector<container>(1000005, initor));
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
		if (sscanf(str.c_str(), "W %u %u", &i, &j) == 2)
		{
			i += 500000;
			container s = container(0, 0);
			s.hasl = s.hasr = 0;
			tree[{i, i + j}] = s;
			auto ans = tree(0, 1000005);
			printf("%u %u\n", ans.count, ans.sum);
		}
		else if (sscanf(str.c_str(), "B %u %u", &i, &j) == 2)
		{
			i += 500000;
			tree[{i, i + j}] = container(1, 1);
			auto ans = tree(0, 1000005);
			printf("%u %u\n", ans.count, ans.sum);
		}
		else
			return 0;
	}
	return 0;
}
