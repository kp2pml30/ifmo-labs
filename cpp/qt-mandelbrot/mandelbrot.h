#pragma once

#include <chrono>
#include <complex>
#include <condition_variable>
#include <queue>
#include <thread>
#include <mutex>
#include <QPainter>
#include <unordered_set>
#include <functional>

class MandelbrotHolder
{
public:
	using PrecType = double;
	// this complex would be used as vec2 as well
	using Complex = std::complex<PrecType>;
private:

	struct Tile;
	friend Tile;

	struct Threading
	{
		struct TileWithPrior
		{
			int prior;
			Tile* tile;

#if defined(__cplusplus) && __cplusplus >=202000
			int operator<=>(TileWithPrior const& r) const noexcept
			{
				return prior - r.prior;
			}
#else
# define MAKEOP(o) \
			bool operator o(TileWithPrior const& r) const noexcept \
			{ \
				return prior - r.prior o 0; \
			}
			MAKEOP(==)
			MAKEOP(!=)
			MAKEOP(<)
			MAKEOP(>)
			MAKEOP(<=)
			MAKEOP(>=)
# undef MAKEOP
#endif
		};

		std::priority_queue<TileWithPrior> tasks;
		std::mutex mut;
		std::condition_variable cv;

		Threading(Threading&&) = delete;
		Threading(Threading const&) = delete;

		struct ThreadData
		{
			std::atomic_bool running = true;
			Threading* thr = nullptr;

			void ThreadFunc();
		};
		std::vector<std::pair<std::thread, ThreadData>> threads;

		Threading(std::size_t size)
		: threads(size)
		{}
	} threading;
	friend Threading;

public:
	struct CoordSys
	{
		Complex zeroPixelCoord = {-2, -2};
		PrecType scale = 1 / 256.0;
		int
			xcoord = 0,
			ycoord = 0;
	};
	CoordSys coordSys;
private:

	struct TileHelper
	{
	public:
		std::vector<Tile*> pool;
		using PixCoord = std::pair<int, int>;
		std::map<PixCoord, Tile*> cache;

		struct {
			std::unique_ptr<Tile> tile;
			int x = 0, y = 0;
			PrecType scale = -1;
		} thumbnail;

		struct {
			QImage pre;
			QImage cur;
			CoordSys cs;
			std::chrono::system_clock::time_point lastUpd = std::chrono::system_clock::now();
		} renderTargets;

		// from main thread only
		TileHelper();
		~TileHelper();
		void InvalidateTiles() noexcept;
		Tile* GetTile(int x, int y, Complex cornder, Complex diag, int power) noexcept;
	private:
		Tile* GetFromPool() noexcept;
		Tile* Allocate() noexcept;

		QImage dflt;
	} tilesData;

	struct UsedTiles
	{
		std::unordered_set<Tile*>
			prev,
			cur,
			used;

		void Add(Tile*) noexcept;
		void Finish() noexcept;
		std::size_t InvalidateCache(TileHelper&) noexcept;
	} usedTiles;

	// to call update
	std::function<void()> scheduler;

	int power = 2;

	void RenderSmth(QPainter& painter, int width, int height);
public:
	MandelbrotHolder(std::function<void()> scheduler);
	void Render(int width, int height);
	void Paint(QPainter& painter);
	void Scale(PrecType by, int width, int height);
	void Move(int dx, int dy);
	void SetPower(int power);

	~MandelbrotHolder();
};

