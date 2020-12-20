// #pragma comment(linker, "/STACK:36777216")

#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdio>
#include <fstream>

using uint = unsigned;

#if !defined(__OPTIMIZE__)
#	include <sstream>
	auto cin = std::stringstream(R"delim(
8
I 2 7 1
I 3 8 -5
I 2 7 -2
Q 2
I 6 8 5
Q 18
Q 4
I 3 7 1

E
)delim");
#else
	using std::cin;
	// std::ifstream cin("crypto.in");
#endif

// i won't clean memory because this task is awful

template<typename t1, typename ...t>
auto maxfunc(t1 a, t ...args)
{
	if constexpr (sizeof...(args) == 0)
		return a;
	else
	{
		auto margs = maxfunc(args...);
		return a > margs ? a : margs;
	}
}
struct container
{
	int ma = 0, full = 0;

	container operator+(const container &r) const
	{
		if (ma == (1 << 31))
			return r;
		if (r.ma == (1 << 31))
			return *this;
		container ret;
		ret.ma = maxfunc(0, full, ma, full + r.ma, full + r.full);
		ret.full = full + r.full;
		return ret;
	}

	bool operator==(const container &r) const { return ma == r.ma && full == r.full; }
};

static const container setn = container({1 << 31, 0});

container SetCombine(container l, container r)
{
	if (r == setn)
			return l;
	return r;
}
container SetCombine(container l, container r, int lx, int rx)
{
	if (r == setn)
		return l;
	if (l == setn)
		return r;
	int m = rx - lx;
	r.full *= m;
	if (r.ma > 0)
		r.ma = r.full;
	else
		r.ma = 0;
	return r;
}

class Tree
{
public:
	class Node
	{
	private:
		friend Tree;
		void Split(int lx, int rx)
		{
			if (rx - lx == 1)
				return;
			const int m = (lx + rx) / 2;
			Propagate(lx, rx);
			left = new Node();
			right = new Node();
			int delta = el.full / (rx - lx);
			left->el.full = delta * (m - lx);
			left->el.ma = left->el.full > 0 ? left->el.full : 0;
			right->el.full = delta * (rx - m);
			right->el.ma = right->el.full > 0 ? right->el.full : 0;
			// left->Split(lx, m);
			// right->Split(m, rx);
		}
	public:
		Node
			*left = nullptr,
			*right = nullptr;

		container
			set = setn,
			el;

		void Propagate(int lx, int rx)
		{
			if (rx - lx == 1)
				return;
			if (set == setn)
				return;
			if (left == nullptr)
			{
				el = SetCombine(el, set, lx, rx);
				set = setn;
				return;
			}
			int m = (lx + rx) / 2;
	 
			left->set = SetCombine(left->set, set);
			left->el  = SetCombine(left->el,  set, lx, m);

			right->set = SetCombine(right->set, set);
			right->el  = SetCombine(right->el,  set, m, rx);

			el = left->el + right->el;
			set = setn;
		}

		void Set(int l, int r, container v, int lx, int rx)
		{
			Propagate(lx, rx);
			if (l >= rx || lx >= r)
				return;
			if (lx >= l && rx <= r)
			{
				set = SetCombine(set, v);
				el = SetCombine(el, v, lx, rx);
				return;
			}
			if (left == nullptr)
				Split(lx, rx);
			int m = (lx + rx) / 2;
			left->Set(l, r, v, lx, m);
			right->Set(l, r, v, m, rx);
			el = left->el + right->el;
		}

		container calc(int l, int r, int lx, int rx)
		{
			Propagate(lx, rx);
			if (l >= rx || lx >= r)
				return container();
			if (lx >= l && rx <= r)
				return el;
			if (left == nullptr)
			{
				int delta = el.full / (rx - lx);
				int vvv = ((int)(r < rx ? r : rx) - (int)(l > lx ? l : lx)) * delta;
				return container({vvv > 0 ? vvv : 0, vvv});
			}
			auto m = (lx + rx) / 2;
			return left->calc(l, r, lx, m) + right->calc(l, r, m, rx);
		}
	};

	Node *head;
	int n;

	Tree(int n)
	{
		n--;
		n |= n >> 1;
		n |= n >> 2;
		n |= n >> 4;
		n |= n >> 8;
		n |= n >> 16;
		n++;
		this->n = n;
		head = new Node();
		// head->Split(0, n);
	}

	void Set(int l, int r, container v) { head->Set(l, r, v, 0, n); }
	container Get(int l, int r) { return head->calc(l, r, 0, n); }
	int TaskI(int q)
	{
		int
			x = 0,
			lx = 0,
			rx = n;
		Node *no = head;
		no->Propagate(lx, rx);
		while (true)
		{
			Node
				*left = no->left,
				*right = no->right;
			if (rx - lx == 1)
				return x - n + 1;
			if (left == nullptr)
			{
				if (no->el.full <= q)
					return n;
				int delta = no->el.full / (rx - lx);
				if (delta <= 0)
					throw "up";
				return lx + (q + 1 + delta - 1) / delta - 1;
			}
			int m = (lx + rx) / 2;
			left->Propagate(lx, m);
			right->Propagate(m, rx);
			if (left->el.ma > q)
			{
				no = left;
				x = 2 * x + 1;
				rx = m;
			}
			else
			{
				q -= left->el.full;
				no = right;
				x = 2 * x + 2;
				lx = m;
			}
		}
	}
};


class setplusoper
{
public:
	container operator()(container l, container r)
	{
		if (r.ma == (1 << 31))
			return l;
		return r;
	}
	container operator()(container l, container r, int lx, int rx)
	{
		if (r.ma == (1 << 31))
			return l;
		if (l.ma == (1 << 31))
			return r;
		int m = rx - lx;
		r.full *= m;
		if (r.ma > 0)
			r.ma = r.full;
		else
			r.ma = 0;
		return r;
	}
};

class mindescr
{
public:
	using type = container;
	std::plus<container> oper;
	setplusoper setoper;
	const type setneutral = container({1 << 31, 0});
	const type    neutral = container();
};

int main(void)
{
	int n;
	cin >> n;
	Tree tree(n + 1);
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
		int i, j;
		int Q;
		if (sscanf(str.c_str(), "I %u %u %i", &i, &j, &Q) == 3)
		{
			tree.Set(i, j + 1, container({Q < 0 ? 0 : Q, Q}));
		}
		else if (sscanf(str.c_str(), "Q %i", &Q) == 1)
		{
			auto ans = tree.TaskI(Q);
			if (ans > n)
				ans = n;
			else
			{
				bool che = true;
				while (ans > 0)
					if (tree.Get(0, ans + 1).ma > Q)
					{
						che = false;
						ans--;
					}
					else
						break;
				if (che)
					while (ans < n)
					{
						if (tree.Get(0, ans + 1).ma <= Q)
							ans++;
						else
							break;
					}
			}
			printf("%u\n", ans);
		}
		else
			return 0;
	}
	return 0;
}
