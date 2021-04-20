#include <cassert>
#include <array>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <algorithm>
#include <map>
#include <functional>
#include <set>
#include <unordered_set>
#include <list>
#include <memory>
#include <deque>
#include <variant>
#include <numeric>
#include <optional>

#ifdef _DEBUG
auto cin = std::stringstream(R"delim(
3 0 3
0 3 3

)delim");
using std::cout;
#else
using std::cin;
using std::cout;
// static auto cin = std::ifstream("matching.in");
// static auto cout = std::ofstream("matching.out");
#endif

using uint = std::uint32_t;
using size_type = std::int64_t;

constexpr auto infflow = 1'000'000'000;

template<typename T>
struct CollectionAllocator
{
private:
	static std::vector<T> cols;
public:

	static T Get()
	{
		if (!cols.empty())
		{
			auto r = std::move(cols.back());
			cols.pop_back();
			return r;
		}
		return T{};
	}

	static void Retract(T&& c)
	{
		c.clear();
		cols.push_back(std::move(c));
	}

	struct Returner
	{
		void operator()(T* t) noexcept
		{
			Retract(std::move(*t));
		}
	};
	using Flush = std::unique_ptr<T, Returner>;
};
template<typename T>
std::vector<T> CollectionAllocator<T>::cols;

struct EdgeData
{
	int flow = 0;
	int capacity;

	EdgeData(int cap = 0)
	: capacity(cap)
	{}
};

struct VertexData
{
};

class Graph
{
public:
	std::vector<VertexData> vertsData;
	std::vector<EdgeData> edgesData;
	struct Connection
	{
		int to;
		int data;
	};
	using VertCons = std::vector<Connection>;
	std::vector<VertCons> verts;

	void SetVers(int count)
	{
		verts.resize(count);
		vertsData.resize(count);
	}

	void AddEdgeDir(int f, int t, EdgeData ed = {})
	{
		verts[f].push_back({ t, (int)edgesData.size() });
		edgesData.push_back(ed);
		ed.capacity = 0;
		verts[t].push_back({ f, (int)edgesData.size() });
		edgesData.push_back(std::move(ed));
	}

	void AddEdge(int a, int b, EdgeData ed = {})
	{
		verts[a].push_back({ b, (int)edgesData.size() });
		edgesData.push_back(ed);
		verts[b].push_back({ a, (int)edgesData.size() });
		edgesData.push_back(std::move(ed));
	}

	void FlowBFS(int root, std::vector<int>& d)
	{
		using QueueProvider = CollectionAllocator<std::vector<int>>;
		auto queue = QueueProvider::Get();
		auto qf123 = QueueProvider::Flush(&queue);

		auto queue_next = QueueProvider::Get();
		auto qf124 = QueueProvider::Flush(&queue_next);
		queue.emplace_back(root);

		while (!queue.empty())
		{
			for (auto const& a : queue)
			{
				for (auto const& b : verts[a])
				{
					auto const& edge = edgesData[b.data];
					if (edge.flow < edge.capacity && d[b.to] == -1)
					{
						d[b.to] = d[a] + 1;
						queue_next.emplace_back(b.to);
					}
				}
			}
			std::swap(queue, queue_next);
			queue_next.clear();
		}
	}

	int FlowDfs(std::vector<int>& ptr, std::vector<int>& d, int f, int dest, int flow)
	{
		if (flow == 0)
			return 0;
		if (f == dest)
			return flow;
		for (; ptr[f] < verts[f].size(); ptr[f]++)
		{
			int
				id = verts[f][ptr[f]].data,
				to = verts[f][ptr[f]].to;
			auto& edge = edgesData[id];
			if (d[to] != d[f] + 1)
				continue;
			if (auto delta = FlowDfs(ptr, d, to, dest, std::min(flow, edge.capacity - edge.flow));
				delta != 0)
			{
				edge.flow += delta;
				edgesData[id ^ 1].flow -= delta;
				return delta;
			}
		}
		return 0;
	}

	int Dinic(int s, int t)
	{
		int flow = 0;

		using DProvider = CollectionAllocator<std::vector<int>>;
		auto d = DProvider::Get();
		auto flush22 = DProvider::Flush(&d);
		auto ptr = DProvider::Get();
		auto flush2123123 = DProvider::Flush(&ptr);

		while (true)
		{
			d.assign(vertsData.size(), -1);
			d[s] = 0;
			FlowBFS(s, d);
			if (d[t] == -1)
				break;
			while (true)
			{
				ptr.assign(vertsData.size(), 0);
				int push = FlowDfs(ptr, d, s, t, infflow);
				if (push == 0)
					break;
				flow += push;
			}
		}
		return flow;
	}
};

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	Graph g;

	g.SetVers(8);

	int r1, s1, p1, r2, s2, p2;
	cin >> r1 >> s1 >> p1 >> r2 >> s2 >> p2;

	g.AddEdgeDir(0, 1, EdgeData(r2));
	g.AddEdgeDir(0, 2, EdgeData(s2));
	g.AddEdgeDir(0, 3, EdgeData(p2));

	g.AddEdgeDir(1, 5, EdgeData(infflow));
	g.AddEdgeDir(2, 6, EdgeData(infflow));
	g.AddEdgeDir(3, 4, EdgeData(infflow));

	g.AddEdgeDir(1, 4, EdgeData(infflow));
	g.AddEdgeDir(2, 5, EdgeData(infflow));
	g.AddEdgeDir(3, 6, EdgeData(infflow));

	g.AddEdgeDir(4, 7, EdgeData(r1));
	g.AddEdgeDir(5, 7, EdgeData(s1));
	g.AddEdgeDir(6, 7, EdgeData(p1));

	cout << r1 + s1 + p1 - g.Dinic(0, 7) << std::endl;

	return 0;
}