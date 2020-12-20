// no dont look

#include <array>
#include <vector>
#include <iostream>
#include <algorithm>
#include <fstream>
#include <cstdint>
#include <cmath>
#include <sstream>
#include <map>
#include <functional>
#include <map>
#include <set>
#include <unordered_set>

#if 0
char MYBUFFER[209715200];
size_t LASTIND;

inline void * operator new (size_t n)
{
	char *res = MYBUFFER + LASTIND;
	LASTIND += n;
	return (void *)res;
}
inline void operator delete (void *) { }
#endif

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
5 1
1 2
2 3
1 4
1 5
)delim");
using std::cout;
#else
using std::cin;
using std::cout;
#endif

using uint = std::uint32_t;
using size_type = std::uint32_t;

struct tree_t
{
	size_type up;
	size_type grandi;
	std::vector<size_type> children;
	std::set<size_type> checked;

	size_type CalcGrandi() noexcept;
	size_type RecalcRootGrandi(size_type diff) noexcept;
	void GetWinEdge(size_type wants) noexcept;
};

std::vector<tree_t> tree;

size_type ROOT;

size_type tree_t::CalcGrandi() noexcept
{
	grandi = 0;
	for (auto& a : children)
		grandi ^= tree[a].CalcGrandi() + 1;
	return grandi;
}

size_type tree_t::RecalcRootGrandi(size_type diff) noexcept
{
	auto cur = this - tree.data();
	while (tree[cur].up != cur)
	{
		if (tree[cur].checked.count(diff) != 0)
			return 1;
		tree[cur].checked.emplace(diff);
		diff = (tree[cur].grandi + 1) ^ ((tree[cur].grandi ^ diff) + 1);
		cur = tree[cur].up;
	}
	return tree[cur].grandi ^ diff;
}

std::map<std::pair<size_type, size_type>, size_type> edges;

[[noreturn]] void PrintAndExit(size_type offseta, size_type offsetb)
{
	// verify
	if constexpr (0)
	{
		for (size_type i = 0; i < tree[offseta].children.size(); i++)
			if (tree[offseta].children[i] == offsetb)
			{
				std::swap(tree[offseta].children[i], tree[offseta].children.back());
				break;
			}
		tree[offseta].children.pop_back();
		if (tree[ROOT].CalcGrandi() != 0)
			throw "down";
	}

	if (offseta > offsetb)
		std::swap(offseta, offsetb);

	auto iter = edges.find({offseta, offsetb});
	if (iter == edges.end())
		throw "up";
	std::cout << iter->second << std::endl;
	exit(0);
}

void tree_t::GetWinEdge(size_type wants) noexcept
{
	for (auto const& a : children)
	{
		/*
		 ? current = wants
		 ! current = (child + 1) ^ other
		 ? current' = (child' + 1) ^ other = wants
		 ? child' = wants ^ other - 1
		 ? child' = wants ^ current ^ (child + 1) - 1
		*/
		auto old = wants ^ grandi ^ (tree[a].grandi + 1);
		if (old == 0)
			PrintAndExit(this - tree.data(), a);
		tree[a].GetWinEdge(old - 1);
	}
}

int main(void)
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	size_type n, r;

	cin >> n >> r;
	r--;

	ROOT = r;

	std::vector<std::vector<size_type>> graph(n);

	for (size_type _ = 0; _ < n - 1; _++)
	{
		size_type a, b;
		cin >> a >> b;
		a--;
		b--;
		if (a > b)
			std::swap(a, b);
		graph[a].emplace_back(b);
		graph[b].emplace_back(a);
		edges.insert({{a, b}, _ + 1});
	}

	tree.resize(n);
	{
		std::function<void(size_type, size_type)> graph2tree = [&](size_type u, size_type from) {
			tree[u].up = from;
			tree[u].children.reserve(graph[u].size());
			for (auto const& a : graph[u])
				if (a != from)
				{
					tree[u].children.emplace_back(a);
					graph2tree(a, u);
				}
		};
		graph2tree(r, r);
	}
	graph.clear();
	graph.shrink_to_fit();

	auto res = tree[r].CalcGrandi();

	if (res == 0)
	{
		cout << 2 << std::endl;
		return 0;
	}

	cout << "1\n";

	tree[r].GetWinEdge(0);

	throw "up";

	return 0;
}