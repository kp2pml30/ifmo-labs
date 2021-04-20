#include <thread>
#include <chrono>

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
4 0
1 2 1 2
1 3 2 2
3 2 1 1
2 4 2 1
3 4 2 3

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
	int cost;

	// int f, t;

	void SetDir(int f1, int t1) noexcept
	{
		// f = f1;
		// t = t1;
	}
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

	void SetVerts(int count)
	{
		verts.resize(count);
		vertsData.resize(count);
	}

	void AddEdgeDirRaw(int f, int t, EdgeData ed = {})
	{
		verts[f].push_back({ t, (int)edgesData.size() });
		edgesData.push_back(std::move(ed));
		edgesData.back().SetDir(f, t);
	}
	void AddEdgeDir(int f, int t, EdgeData ed = {})
	{
		AddEdgeDirRaw(f, t, ed);
		ed.capacity = 0;
		ed.cost *= -1;
		AddEdgeDirRaw(t, f, ed);
	}

	void AddEdge(int a, int b, EdgeData ed = {})
	{
		AddEdgeDirRaw(a, b, ed);
		AddEdgeDirRaw(b, a, ed);
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

	void ResetFlow() noexcept
	{
		for (auto& e : edgesData)
			e.flow = 0;
	}

	// expects that flow was found before
	void MinCost() noexcept
	{
		auto myCon = verts;
		auto myConFilter = [&myCon, this]() {
			for (auto& vcon : myCon)
			{
				for (int a = 0; a < vcon.size(); a++)
					while (true)
					{
						if (a < vcon.size())
							break;
						auto& dat = edgesData[vcon[a].data];
						if (dat.capacity - std::abs(dat.flow) > 0)
							break;
						std::swap(vcon[a], vcon.back());
						vcon.pop_back();
					}
			}
		};

		auto getDescr = [&](int e) -> EdgeData {
			int takefrom = e & ~1;
			EdgeData ret = edgesData[takefrom];
			ret.cost = edgesData[e].cost;
			ret.flow = 0;
			if (e & 1)
			{
				ret.capacity = -edgesData[e].flow;
			}
			else
			{
				ret.capacity = edgesData[e].capacity - edgesData[e].flow;
			}
			return ret;
		};

		int n = myCon.size();
		std::vector<std::int64_t> d;
		std::vector<int> p;
		std::vector<int> eno;

		std::vector<int> negcycle;
		std::vector<int> edgecycles;

		while (true)
		{
			d.assign(n, 0);
			p.assign(n, -1);
			eno.assign(n, -1);

			int relaxed = -1;

			for (size_type _ = 0; _ < n; _++)
			{
				relaxed = -1;
				for (size_type i = 0; i < n; i++)
					for (auto const& e : myCon[i])
					{
						auto desc = getDescr(e.data);
						if (desc.capacity - desc.flow <= 0)
							continue;
						if (d[e.to] > d[i] + desc.cost)
						{
							p[e.to] = i;
							eno[e.to] = e.data;
							d[e.to] = d[i] + desc.cost;
							relaxed = e.to;
						}
					}
			}
			if (relaxed == -1)
				break;

			negcycle.clear();
			edgecycles.clear();

			std::set<int> visited;
			visited.emplace(relaxed);
			negcycle.push_back(relaxed);
			edgecycles.push_back(eno[relaxed]);
			while (true)
			{
				relaxed = p[relaxed];
				if (relaxed == -1)
					throw "up";
				if (!visited.emplace(relaxed).second)
					break;
				negcycle.push_back(relaxed);
				edgecycles.push_back(eno[relaxed]);
			}

			int start_from = 0;
			while (negcycle[start_from] != relaxed)
				start_from++;

			auto minflow = std::numeric_limits<int>::max();

			for (int i = negcycle.size() - 1; i >= start_from; i--)
			{
				auto const& edge = getDescr(edgecycles[i]);
				minflow = std::min(minflow, edge.capacity - std::abs(edge.flow));
			}
			for (int i = negcycle.size() - 1; i >= start_from; i--)
			{
				if (edgecycles[i] & 1)
				{
					edgesData[edgecycles[i]].flow += minflow;
					edgesData[edgecycles[i] & ~1].flow -= minflow;
				}
				else
				{
					edgesData[edgecycles[i]].flow += minflow;
					edgesData[edgecycles[i] | 1].flow -= minflow;
				}
			}
		}
	}
};

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	Graph g;

	int n;
	cin >> n;
	g.SetVerts(n);
	{
		int m;
		cin >> m;
		while (m-- > 0)
		{
			int f, t, cap, cost;
			cin >> f >> t >> cap >> cost;
			f--; t--;
			EdgeData me;
			me.flow = 0;
			me.capacity = cap;
			me.cost = cost;
			g.AddEdgeDir(f, t, me);
		}
	}

	g.Dinic(0, n - 1);

	g.MinCost();

	std::uint64_t ans = 0;

	for (int i = 0; i < (int)g.edgesData.size() - 1; i += 2)
		ans += (std::int64_t)std::abs(g.edgesData[i].flow) * g.edgesData[i].cost;

	cout << ans << std::endl;

	return 0;
}