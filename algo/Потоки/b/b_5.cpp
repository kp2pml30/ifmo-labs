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
3 3
1 2 3
1 3 5
3 2 7


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

struct Empty {};
struct EmptyEdgeData
{
	void Set(int f, int t) {}
	void SetDir(int f, int t) {}
};

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

void Abort() noexcept
{
	throw "up";
}

template<typename VertexData = Empty, typename EdgeData = EmptyEdgeData>
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
		ed.SetDir(f, t);
		verts[f].push_back({ t, (int)edgesData.size() });
		edgesData.push_back(std::move(ed));
	}

	void AddEdge(int a, int b, EdgeData ed = {})
	{
		ed.Set(a, b);
		ed.SetDir(a, b);
		verts[a].push_back({ a, (int)edgesData.size() });
		verts[b].push_back({ b, (int)edgesData.size() });
		edgesData.push_back(std::move(ed));
	}

	/*
	 * FVert :: (Graph, vert int) -> bool
	 * FEdge :: (Graph, vert from int, vert to int, EdgeData) -> bool
	 */
	template<typename FVert, typename FEdge>
	bool BFS(int root, FVert const& fVert, FEdge const& fEdge)
	{
		using VisitedProvider = CollectionAllocator<std::unordered_set<int>>;
		auto visited = VisitedProvider::Get();
		auto vf123 = VisitedProvider::Flush(&visited);
		visited.emplace(root);

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
				if (fVert(*this, a))
					return true;
				for (auto const& b : verts[a])
					if (visited.emplace(b.to).second)
					{
						if (fEdge(*this, a, b.to, edgesData[b.data]))
							return true;
						queue_next.emplace_back(b.to);
					}
			}
			std::swap(queue, queue_next);
			queue_next.clear();
		}
		return false;
	}

	/*
	 * FVert :: (Graph, vert int, A) -> bool
	 * FEdge :: (Graph, vert from int, vert to int, EdgeData, A) -> A
	 */
	template<typename FVert, typename FEdge, typename A>
	bool DFS(int f, FVert const& fVert, FEdge const& fEdge, A const& data)
	{
		if (fVert(*this, f))
			return true;
		for (auto const& t : verts[f])
		{
			if (DFS(t.to, fVert, fEdge, fEdge(*this, f, t.to, edgesData[t.ind], data)))
				return true;
		}
		return false;
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
				int push = FlowDfs(ptr, d, s, t, 1'000'000'000);
				if (push == 0)
					break;
				flow += push;
			}
		}
		return flow;
	}
};

struct MyEdgeData
{
	int flow = 0;
	int capacity = 0;
	int f, t;
	void Set(int f, int t)
	{
		this->f = f;
		this->t = t;
	}
	void SetDir(int f, int t)
	{
		this->f = f;
		this->t = t;
	}
};

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	Graph<Empty, MyEdgeData> g;

	int n;
	cin >> n;
	g.SetVers(n);
	{
		int m;
		cin >> m;
		while (m-- > 0)
		{
			int f, t, cap;
			cin >> f >> t >> cap;
			f--; t--;
			MyEdgeData me;
			me.flow = 0;
			me.capacity = cap;
			g.AddEdgeDir(f, t, me);
			me.flow = 0;
			me.capacity = cap;
			g.AddEdgeDir(t, f, me);
		}
	}

	auto cap = g.Dinic(0, n - 1);

	auto visited = std::vector<bool>(n, false);
	visited[0] = true;
	auto dfs = [&](auto const& self, int f) -> void {
		for (auto const& to : g.verts[f])
			if (auto eind = to.data; !visited[to.to] && g.edgesData[eind].flow < g.edgesData[eind].capacity)
			{
				visited[to.to] = true;
				self(self, to.to);
			}
	};
	dfs(dfs, 0);

	std::set<int> answer;

	for (int i = 0; i < g.edgesData.size(); i++)
		if (visited[g.edgesData[i].f] != visited[g.edgesData[i].t])
			answer.emplace(i / 2);

	cout << answer.size() << ' ' << cap << '\n';

	for (auto const& a : answer)
		cout << a + 1 << ' ';

	cout << std::endl;

	return 0;
}