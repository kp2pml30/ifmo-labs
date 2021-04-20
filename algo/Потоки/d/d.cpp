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
5 5
---#-
A--#-
####-
--.--
--.-B



)delim");
using std::cout;
#else
using std::cin;
using std::cout;
// static auto cin = std::ifstream("matching.in");
// static auto cout = std::ofstream("matching.out");
#endif

// #define EOLYMP

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
	cost_t cost;

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
				o
					<< "v" << ind
					<< " -> "
					<< "v" << e.to
					<< " [label=\""
					// << "$=" << ed.cost
					<< " c=" << ed.capacity
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
};

int main()
{
	std::ios_base::sync_with_stdio(false);
	cin.tie(nullptr);

	int h, w;
	cin >> h >> w;

	auto table = std::vector<std::string>();
#if !defined(EOLYMP)
	{
		std::string str;
		std::getline(cin, str);
	}
	for (int row = 0; row < h; row++)
	{
		std::string str;
		std::getline(cin, str);
		if (str.size() != w)
			throw "up";
		table.emplace_back(std::move(str));
	}
#else
	std::swap(w, h);
	{
		table = std::vector<std::string>(h, std::string(w, '-'));
		int k, l;
		cin >> k >> l;
		int x, y;
		for (int i = 0; i < k; i++)
		{
			cin >> x >> y;
			x--; y--;
			table[y][x] = '#';
		}
		for (int i = 0; i < l; i++)
		{
			cin >> x >> y;
			x--; y--;
			table[y][x] = '.';
		}
		cin >> x >> y;
		x--; y--;
		table[y][x] = 'A';
		cin >> x >> y;
		x--; y--;
		table[y][x] = 'B';
	}
#endif

	Graph g;
	g.SetVerts(w * h * 2);

	auto const& indFByRC = [w](int row, int col) {
		return row * w + col;
	};

	auto const& indTByRC = [w, h](int row, int col) {
		return w * h + row * w + col;
	};

	auto const& RCByInd = [w, h](int ind) {
		if (ind >= w * h)
			ind -= w * h;
		return std::make_pair(ind / w, ind % w);
	};

	int s = -1, e = -1;

	for (int row = 0; row < h; row++)
		for (int col = 0; col < w; col++)
		{
			const auto current_char = table[row][col];
			if (current_char == '#')
				continue;
			if (current_char == 'A')
				s = indTByRC(row, col);
			else if (current_char == 'B')
			{
				e = indFByRC(row, col);
				continue;
			}
			else
			{
				EdgeData ed;
				ed.capacity = current_char == '-' ? infflow : 3;
				g.AddEdgeDir(indFByRC(row, col), indTByRC(row, col), ed);
			}
			auto const& addDelta = [&](int dr, int dc) {
				const int nr = row + dr;
				const int nc = col + dc;
				if (nr < 0 || nr >= h || nc < 0 || nc >= w)
					return;
				if (table[nr][nc] == 'A' || table[nr][nc] == '#')
					return;
				EdgeData ed;
				ed.capacity = infflow;
				g.AddEdgeDir(indTByRC(row, col), indFByRC(nr, nc), ed);
			};
			addDelta( 0, +1);
			addDelta( 0, -1);
			addDelta(+1,  0);
			addDelta(-1,  0);
		}

	auto cap = g.Dinic(s, e);

	// cout << g << std::endl;

	if (cap >= infflow)
	{
		cout << -1 << std::endl;
		return 0;
	}

	// if (cap == 0)
	// {
	// 	for (auto const& a : table)
	// 		cout << a << '\n';
	// 	cout << std::flush;
	// 	return 0;
	// }

	auto visited = std::vector<bool>(w * h * 2, false);
	auto dfs = [&](auto const& self, int f) -> void {
		for (auto const& to : g.verts[f])
			if (auto eind = to.data; !visited[to.to] && g.edgesData[eind].flow < g.edgesData[eind].capacity)
			{
				visited[to.to] = true;
				self(self, to.to);
			}
	};
	visited[s] = true;
	dfs(dfs, s);

	int ANC = 0;

	for (int i = 0; i < g.edgesData.size(); i++)
		if (auto const& ed = g.edgesData[i]; visited[ed.f] != visited[ed.t])
		{
			if (ed.t == e || ed.f == s || ed.flow <= 0)
				continue;
			auto [r, c] = RCByInd(ed.t);
			if (table[r][c] != '.')
			{
				for (auto const& a : table)
					cout << a << '\n';
				throw "up";
			}
			table[r][c] = '+';
			ANC++;
		}

	cout << ANC << '\n';
#if	!defined(EOLYMP)
	for (auto const& a : table)
		cout << a << '\n';
#else
	for (int y = 0; y < h; y++)
		for (int x = 0; x < w; x++)
			if (table[y][x] == '+')
				cout << y + 1 << ' ' << x + 1 << '\n';
#endif

	cout << std::flush;

	return 0;
}