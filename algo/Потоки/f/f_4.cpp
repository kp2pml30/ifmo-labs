#include <cassert>
#include <array>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <iomanip>
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
4
#...
.#..
..#.
...#
8 6 3 1

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
using cost_t = std::int64_t;
using flow_t = std::int64_t;

constexpr flow_t infflow = 1'000'000'000;

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

#if defined(_DEBUG) || 1
#define USE_FT
#endif

struct EdgeData
{
	flow_t flow = 0;
	flow_t capacity;
	flow_t minflow = 0;
	cost_t cost = 0;

#ifdef USE_FT
	int f, t;
#endif

	void SetDir(int f1, int t1) noexcept
	{
#ifdef USE_FT
		f = f1;
		t = t1;
#endif
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
		ed.flow *= -1;
		ed.cost *= -1;
		AddEdgeDirRaw(t, f, ed);
	}

	void AddEdge(int a, int b, EdgeData ed = {})
	{
		AddEdgeDirRaw(a, b, ed);
		ed.flow *= -1;
		ed.cost *= -1;
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

	flow_t FlowDfs(std::vector<int>& ptr, std::vector<int>& d, int f, int dest, flow_t flow)
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
		flow_t flow = 0;

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
				auto push = FlowDfs(ptr, d, s, t, infflow);
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
			EdgeData const& me = edgesData[e];
			EdgeData const& co = edgesData[e ^ 1];
			ret.capacity = me.capacity - me.flow;
			return ret;
		};

		int n = myCon.size();
		std::vector<cost_t> d;
		std::vector<int> p;
		std::vector<int> eno;

		std::vector<int> negcycle;
		std::vector<int> edgecycles;

		while (true)
		{
			//if (std::chrono::duration<double, std::milli>(std::chrono::system_clock::now() - start_t).count() > 1500)
			//	throw "up";

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

			auto minflow = std::numeric_limits<flow_t>::max();

			for (int i = negcycle.size() - 1; i >= start_from; i--)
			{
				auto const& edge = getDescr(edgecycles[i]);
				minflow = std::min(minflow, edge.capacity - std::abs(edge.flow));
			}
			for (int i = negcycle.size() - 1; i >= start_from; i--)
			{
				if ((edgecycles[i] & 1))
				{
					edgesData[edgecycles[i]].flow += minflow;
					edgesData[edgecycles[i] ^ 1].flow -= minflow;
				}
				else
				{
					edgesData[edgecycles[i]].flow += minflow;
					edgesData[edgecycles[i] ^ 1].flow -= minflow;
				}
			}
		}
	}

	std::tuple<flow_t, cost_t> MinCostMaxFlow(int start, int end) {
		flow_t maxFlow = 0;
		cost_t minCost = 0;
		auto id = std::vector<char>();
		auto d = std::vector<flow_t>();
		auto ptr = std::vector<EdgeData*>();
		auto queue = std::deque<int>();
		while (true)
		{
			queue.clear();
			id.assign(verts.size(), 0);
			d.assign(verts.size(), infflow);
			ptr.resize(verts.size());

			d[start] = 0;
			queue.push_back(start);

			while (!queue.empty())
			{
				auto const u = queue.front();
				queue.pop_front();
				id[u] = 2;

				for (auto const& e : verts[u])
					if (auto const& edge = edgesData[e.data];
						edge.flow < edge.capacity && d[edge.t] > d[edge.f] + edge.cost)
				{
					d[edge.t] = d[edge.f] + edge.cost;

					if (!id[edge.t])
						queue.push_back(edge.t);
					else if (id[edge.t] == 2)
						queue.push_front(edge.t);

					id[edge.t] = 1;
					ptr[edge.t] = &edgesData[e.data];
				}
			}

			if (d[end] == infflow)
				break;

			flow_t delta = infflow;

			for (int u = end; u != start; u = ptr[u]->f)
			{
				auto const& edge = *ptr[u];
				delta = std::min(delta, edge.capacity - edge.flow);
			}

			for (int u = end; u != start; u = ptr[u]->f)
			{
				auto& edge = *ptr[u];
				auto& reversed = edgesData[(ptr[u] - edgesData.data()) ^ 1];

				edge.flow += delta;
				reversed.flow -= delta;

				minCost += delta * edge.cost;
			}

			maxFlow += delta;
		}

		return { maxFlow, minCost };
	}

	friend std::ostream& operator<<(std::ostream& o, Graph const& g)
	{
		o << "digraph G{";
		auto visited = std::vector<bool>(g.verts.size());
		auto const& dfs = [&](auto const& dfs, int ind) {
			if (visited[ind])
				return;
			visited[ind] = true;
			for (auto const& e : g.verts[ind])
			{
				auto const& ed = g.edgesData[e.data];
				if (ed.capacity <= 0)
					continue;
				o
					<< "v" << ind
					<< " -> "
					<< "v" << e.to
					<< " [label=\""
					<< " c=" << ed.capacity
					<< "$=" << ed.cost
					<< "m=" << ed.minflow
					<< " f=" << ed.flow
					<< "\""
					;
				if (ed.flow > 0)
					o << ", color=red";
				else if (ed.flow < 0)
					o << ", color=blue";
				else if (ed.capacity == 0)
					o << ", color=yellow";
				o
					<< "];"
					;
				dfs(dfs, e.to);
			}
		};
		for (int i = 0; i < g.verts.size(); i++)
			dfs(dfs, i);
		o << '}';
		return o;
	}

	std::tuple<int, int, Graph> MakeCirculation() const
	{
		Graph ret;
		const int start = verts.size();
		const int end = verts.size() + 1;
		ret.SetVerts(verts.size() + 3);
		for (auto const& e : edgesData)
		{
			if (e.minflow != 0)
			{
				EdgeData ed;
				ed.capacity = e.minflow;
				ret.AddEdgeDir(start, e.t, ed);
				ret.AddEdgeDir(e.f, end, ed);
			}
			if (e.capacity > e.minflow)
			{
				EdgeData ed;
				ed.cost = e.cost;
				ed.capacity = e.capacity - e.minflow;
				ret.AddEdgeDir(e.f, e.t, ed);
			}
		}
		return { start, end, std::move(ret) };
	}
};

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	int n;
	cin >> n;

	{
		std::string s;
		std::getline(cin, s);
	}

	Graph g;
	g.SetVerts(n + n * n + 2);

	auto getVacant = [f = n + 2]() mutable {
		return f++;
	};

	auto const& getInd = [](int i) {
		return 2 + i;
	};

	int s = 0;
	int e = 1;

	auto points = std::vector<int>(n, 0);

	auto table = std::vector<std::string>();

	auto expectedFlow = 0LL; // std::int64_t(n)* n * 3;
	for (int row = 1; row <= n; row++)
		expectedFlow += row - 1;
	expectedFlow *= 3;

	for (int row = 0; row < n; row++)
	{
		std::string str;
		std::getline(cin, str);
		for (int col = 0; col < row; col++)
		{
			const auto match_result = str[col];
			if (match_result == '.')
			{
				auto vac = getVacant();
				EdgeData ed;
				ed.cost = 0;
				ed.capacity = 3;
				g.AddEdgeDir(s, vac, ed);
				g.AddEdgeDir(vac, getInd(col), ed);
				g.AddEdgeDir(vac, getInd(row), ed);
				continue;
			}
			int w = row;
			int l = col;
			if (match_result == 'l' || match_result == 'L')
				std::swap(w, l);
			if (match_result == 'L' || match_result == 'W')
			{
				points[w] += 3;
			}
			else
			{
				points[w] += 2;
				points[l] += 1;
			}
			expectedFlow -= 3;
		}
		table.emplace_back(std::move(str));
	}


	for (int i = 0; i < n; i++)
	{
		int p;
		cin >> p;
		int delta = p - points[i];
		if (delta < 0)
		{
			cout << "bad_delta\n";
			return 0;
			// throw "up";
		}
		if (delta == 0)
			continue;
		EdgeData ed;
		ed.capacity = delta;
		ed.cost = 0;
		g.AddEdgeDir(getInd(i), e, ed);
	}

	if (auto [flow, cost] = g.MinCostMaxFlow(s, e); flow != expectedFlow)
	{
		cout << "asfsafdsf\n";
		return 0;
		// throw "up";
	}

	for (int v = n + 2; v < g.verts.size(); v++)
	{
		auto const& vd = g.verts[v];
		if (vd.size() == 0)
			break;
		if (vd.size() != 3)
		{
			cout << "kokoko\n";
			return 0;
			// throw "up";
		}
		auto const& e1 = vd[1];
		auto const& e2 = vd[2];
		auto const f1 = g.edgesData[e1.data].flow;
		auto const f2 = g.edgesData[e2.data].flow;
		if (f1 + f2 != 3)
		{
			cout << "!!!\n";
			return 0;
			// throw "up";
		}
		const auto t1 = e1.to - 2;
		const auto t2 = e2.to - 2;
		if (f1 == 3)
		{
			table[t1][t2] = 'W';
			table[t2][t1] = 'L';
		}
		else if (f1 == 2)
		{
			table[t1][t2] = 'w';
			table[t2][t1] = 'l';
		}
		else if (f1 == 1)
		{
			table[t1][t2] = 'l';
			table[t2][t1] = 'w';
		}
		else
		{
			table[t1][t2] = 'L';
			table[t2][t1] = 'W';
		}
	}

	for (auto const& s : table)
		cout << s << '\n';

	return 0;
}