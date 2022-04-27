// internal header/cpp
#pragma once

#include "mandelbrot.h"

struct MandelbrotHolder::Tile
{
public:
	static constexpr int size = 256;

	std::atomic<QImage*> rendered;
	std::atomic_bool running = false;

	enum UpdateStatus
	{
		UPDATED,
		INTERRUPTED,
		INTERRUPT_AND_PUT,
		DONE
	};
private:
	QImage* dflt;
	std::array<QImage, 4> mips;
	int currentMip = 0;
	int currentY = 0;
	int power = 2;
	Complex corner, diag;
	std::mutex mut;

	bool interrupt = false;
	UpdateStatus retStatus = INTERRUPTED;

	friend MandelbrotHolder;

	static std::uint8_t mand(Complex c, int power) noexcept
	{
		if (c.real() >= -0.5 && c.real() <= 0.25
				&& c.imag() >= -0.5 && c.imag() <= 0.5)
			return 0;
		Complex z = {0, 0};

		constexpr int MSTEPS = 255;
		for (int i = 0; i < MSTEPS; i++)
			if (std::norm(z) >= std::norm(Complex(2, 0))) // fast math removes sqrt, but anyway
				return i % 64;
			else
				z = std::pow(z, power) + c;
		return 0;
	}
public:
	Tile(QImage* dflt) : dflt(dflt), rendered(dflt)
	{
		mips[0] = QImage(size / 16, size / 16, QImage::Format::Format_RGB888);
		mips[1] = QImage(size /  8, size /  8, QImage::Format::Format_RGB888);
		mips[2] = QImage(size /  2, size /  2, QImage::Format::Format_RGB888);
		mips[3] = QImage(size, size, QImage::Format::Format_RGB888);
	}
	Tile(Tile const&) = delete;
	Tile(Tile&&) = delete;
	void operator=(Tile const&) = delete;
	void operator=(Tile&&) = delete;

	void Interrupt(UpdateStatus st = INTERRUPTED)
	{
		if (!running.load())
			return;
		// here running may be swithced to false, but it is ok
		auto locker = std::lock_guard(mut);
		interrupt = true;
		retStatus = st;
	}

	// thread safe
	int GetPrior(QImage const* img) const noexcept
	{
		if (img == dflt)
			return mips.size() + 1;
		return mips.size() - (img - &mips.front());
	}
	// thread safe
	bool IsLast(QImage const* img) const noexcept
	{
		return img == &mips.back();
	}
	// thread safe
	bool IsDflt(QImage const* img) const noexcept
	{
		return img == dflt;
	}

	// to call from main thread
	void Set(Complex corner, Complex diag, int power) noexcept
	{
		Interrupt();
		auto locker = std::lock_guard(mut);
		this->corner = corner;
		this->diag = diag;
		this->power = power;
		currentMip = 0;
		currentY = 0;

		rendered.store(dflt);
	}
	// to call from drawer
	UpdateStatus Update() noexcept
	{
		int yd = 0;
		std::unique_ptr<Tile, std::function<void(Tile*)>> runningResetter = {this, [](Tile* a) { a->running.store(false); }};
		Complex mdiag, mcorner;
		std::size_t mcurrentMip;
		while (true)
		{
			int y;
			{
				auto lk = std::lock_guard(mut);
				if (currentMip == mips.size())
					return DONE;
				if (interrupt)
				{
					interrupt = false;
					return retStatus;
				}
				mdiag = diag;
				mcorner = corner;
				// may fire only during first iteration
				currentY += yd;
				if (currentY == mips[currentMip].height())
				{
					rendered.store(&mips[currentMip]);
					currentY = 0;
					currentMip++;
					if (currentMip == mips.size())
						return DONE;
					return UPDATED;
				}
				y = currentY;
				mcurrentMip = currentMip;
			}

			yd = 1;

			auto& img = mips[mcurrentMip];
			int
				h = img.height(),
				w = img.width();

			std::uint8_t* data = img.bits() + y * img.bytesPerLine();
			auto yy = (PrecType)y / h * mdiag.imag() + mcorner.imag();
			for (int x = 0; x < w; x++)
			{
				auto xx = (PrecType)x / w * mdiag.real() + mcorner.real();
				auto val = mand({xx, yy}, power);
				data[x * 3 + 0] = val * 4;
				data[x * 3 + 1] = val / 2;
				data[x * 3 + 2] = val % 3 * 127;
			}
		}
	}
};

void MandelbrotHolder::UsedTiles::Add(Tile* t) noexcept
{
	cur.emplace(t);
}
void MandelbrotHolder::UsedTiles::Finish() noexcept
{
	for (auto& a : prev)
		if (cur.count(a) == 0)
			a->Interrupt();
	std::swap(cur, prev);
	cur.clear();
	used.clear();
}

std::size_t MandelbrotHolder::UsedTiles::InvalidateCache(TileHelper& th) noexcept
{
	std::size_t inv = 0;
	auto it = th.cache.begin();
	while (it != th.cache.end())
		if (used.count(it->second) == 0)
		{
			Tile* t = it->second;
			t->Interrupt();
			it = th.cache.erase(it);
			th.pool.push_back(t);
			inv++;
		}
		else
		{
			++it;
		}
	return inv;
}
