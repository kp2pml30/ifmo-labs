#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdio>

using uint = unsigned;

#if !defined(__OPTIMIZE__)
#	include <sstream>
	auto cin = std::stringstream(R"delim(5
1 2 3 4 5
sum 2 5
sum 1 5
sum 1 4
sum 2 4
set 1 10
set 2 3
set 5 2
sum 2 5
sum 1 5
sum 1 4
sum 2 4
)delim");
#else
	using std::cin;
#endif

template<typename type>
class Tree
{
private:
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
			elements[i] = elements[2 * i + 1] + elements[2 * i + 2];
		}
	}
	long long sum(uint l, uint r, uint x, uint lx, uint rx)
	{
		if (l >= rx || lx >= r)
			return 0;
		if (lx >= l && rx <= r)
			return elements[x];
		uint m = (lx + rx) / 2;
		return sum(l, r, 2 * x + 1, lx, m) + sum(l, r, 2 * x + 2, m, rx);
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
		elements.resize(2 * n - 1, 0);
		for (uint i = 0; i < els.size(); i++)
			elements[n - 1 + i] = els[i];
		for (int i = n - 2; i >= 0; i--)
			elements[i] = elements[2 * i + 1] + elements[2 * i + 2];
	}
	Setter operator[](uint i) { return Setter(this, i); }

	long long operator()(uint l, uint r)
	{
		return sum(l, r, 0, 0, n);
	}
};

int main(void)
{
	uint n;
	cin >> n;
	std::vector<long long> els(n);
	for (uint i = 0; i < n; i++)
		cin >> els[i];
	Tree<long long> tree(els);
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
		if (sscanf(str.c_str(), "set %u %lld", &i, &x) == 2)
		{
			i--;
			tree[i] = x;
		}
		else if (sscanf(str.c_str(), "sum %u %u", &i, &j) == 2)
		{
			i--;
			printf("%lld\n", tree(i, j));
		}
		else
			return 0;
	}
	return 0;
}
