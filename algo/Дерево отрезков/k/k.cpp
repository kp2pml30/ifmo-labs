#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdio>
#include <fstream>

using uint = unsigned;

#if !defined(__OPTIMIZE__)
#	include <sstream>
	auto cin = std::stringstream(R"delim(
3 5
enter 1
enter 1
exit 1
enter 2
enter 2
)delim");
#else
	// using std::cin;
	std::ifstream cin("parking.in");
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
	type sum(uint l, uint r, uint x, uint lx, uint rx)
	{
		if (l >= rx || lx >= r)
			return 0;
		if (lx >= l && rx <= r)
			return elements[x];
		uint m = (lx + rx) / 2;
		return sum(l, r, 2 * x + 1, lx, m) + sum(l, r, 2 * x + 2, m, rx);
	}
	uint search(uint fo, uint x, uint lx, uint rx)
	{
		if (elements[x] == 0)
			return -1;
		if (rx - lx == 1)
			return x;
		uint m = (lx + rx) / 2;
		if (fo >= m && fo < rx)
			return  search(fo, 2 * x + 2, m, rx);
		uint r1 = search(fo, 2 * x + 1, lx, m);
		if (r1 != (uint)-1)
			return r1;
		return search(fo, 2 * x + 2, m, rx);
	}
	uint leftsearch(uint x, uint lx, uint rx)
	{
		if (elements[x] == 0)
			return -1;
		if (rx - lx == 1)
			return x;
		uint m = (lx + rx) / 2;
		uint r1 = leftsearch(2 * x + 1, lx, m);
		if (r1 != (uint)-1)
			return r1;
		return leftsearch(2 * x + 2, m, rx);
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
	uint findplace(uint e)
	{
		uint r1 = search(e, 0, 0, n);
		if (r1 != (uint)-1)
			return r1 + 1 - n;
		return leftsearch(0, 0, n) + 1 - n;
	}
};

int main(void)
{
	freopen("parking.out", "w", stdout);
	uint n, m;
	cin >> n >> m;
	Tree<uint> tree(std::vector<uint>(n, 1));
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
		uint i;
		if (sscanf(str.c_str(), "enter %u", &i) == 1)
		{
			i--;
			uint j = tree.findplace(i);
			tree[j] = 0;
			printf("%u\n", j + 1);
		}
		else if (sscanf(str.c_str(), "exit %u", &i) == 1)
		{
			i--;
			tree[i] = 1;
		}
		else
		{
			fclose(stdout);
			return 0;
		}
	}
	fclose(stdout);
	return 0;
}
