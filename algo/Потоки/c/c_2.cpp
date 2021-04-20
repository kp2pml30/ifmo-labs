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
7 6 1 7
1 2
1 3
2 4
3 4
4 7
4 7

5 7
6 7

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
	int capacity = 0;
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
			d.assign(vertsData.size() , -1);
			d[s] = 0;
			FlowBFS(s, d);
			if (d[t] == -1)
				break;
			while (true)
			{
				ptr.assign(vertsData.size(), 0);
				int push = FlowDfs(ptr, d, s, t, 1'000'000'000);
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

	int n, m, s, t;
	cin >> n >> m >> s >> t;
	if (s == t)
	{
		cout << "YES\n" << s << '\n' << s << std::endl;
		return 0;
	}
	g.SetVers(n + 2);
	while (m-- > 0)
	{
		int f, t;
		cin >> f >> t;
		if (f == t)
			continue;
		EdgeData me;
		me.flow = 0;
		me.capacity = 1;
		g.AddEdgeDir(f, t, me);
	}
	{
		EdgeData me;
		me.flow = 0;
		me.capacity = 2;
		g.AddEdgeDir(0, s, me);
		g.AddEdgeDir(t, n + 1, me);
	}

	if (g.Dinic(0, n + 1) != 2)
	{
		cout << "NO\n";
		return 0;
	}
	cout << "YES\n";

	std::unordered_set<int> bitch;

	auto go = [&]() {
		int cur = s;
		while (cur != n + 1)
		{
			cout << cur << ' ';
			bool good = false;
			for (auto const& b : g.verts[cur])
				if (auto eind = b.data; g.edgesData[eind].flow > 0
					&& bitch.count(eind) == 0)
				{
					cur = b.to;
					if (b.to != n + 1)
					{
						bitch.emplace(eind);
						bitch.emplace(eind ^ 1);
					}
					good = true;
					break;
				}
			if (!good)
				throw "up";
		}
		cout << '\n';
	};
	go();
	go();

	cout << std::flush;

	return 0;
}