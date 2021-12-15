#include <cassert>
#include <cmath>
#include <algorithm>
#include "SeamCarver.h"

SeamCarver::SeamCarver(Image image)
    : m_image(std::move(image))
{}

const Image& SeamCarver::GetImage() const
{
    return m_image;
}

size_t SeamCarver::GetImageWidth() const
{ return m_image.GetWidth(); }

size_t SeamCarver::GetImageHeight() const
{ return m_image.GetHeight(); }

std::tuple<std::size_t, std::size_t> SeamCarver::GetImageSize() const
{ return {GetImageWidth(), GetImageHeight()}; }

std::tuple<std::size_t, std::size_t> SeamCarver::CoordinateToImage(std::ptrdiff_t columnId, std::ptrdiff_t rowId) const
{
    // not auto [] because of type
    const std::ptrdiff_t
            w = GetImageWidth(),
            h = GetImageHeight();
    return {(columnId + w) % w, (rowId + h) % h};
}

Image::Pixel SeamCarver::GetImagePixel(std::size_t columnId, std::size_t rowId) const
{
    return m_image.GetPixel(columnId, rowId);
}

namespace {
/* it would be better to write full math vector API, but
 * 1) it is not a part of the task
 * 2) it is better to use some common API (like Eigen)
 */
struct FloatPixel
{
    float x, y, z;

    FloatPixel(float x, float y, float z)
    : x(x), y(y), z(z)
    {}

    // implicit
    FloatPixel(const Image::Pixel &p)
    : FloatPixel(p.m_blue, p.m_green, p.m_red)
    {}

    template<typename T>
    static FloatPixel BinaryOperation(const FloatPixel &l, const FloatPixel &r, T f)
    { return FloatPixel(f(l.x, r.x), f(l.y, r.y), f(l.z, r.z)); }

    template<typename T>
    static FloatPixel UnaryOperation(const FloatPixel &p, T f)
    { return FloatPixel(f(p.x), f(p.y), f(p.z)); }

    template<typename T>
    float Reduce(T f) const
    { return f(f(x, y), z); }
};
}

double SeamCarver::GetPixelEnergy2(size_t columnId, size_t rowId) const
{
    auto image_pixel_getter = [this](auto ... args)
    {
        return GetImagePixel(args...);
    };
    FloatPixel
        dx = FloatPixel::BinaryOperation(
                std::apply(image_pixel_getter, CoordinateToImage(columnId + 1, rowId)),
                std::apply(image_pixel_getter, CoordinateToImage((std::ptrdiff_t)columnId - 1, rowId)),
                std::minus<float>()),
        dy = FloatPixel::BinaryOperation(
            std::apply(image_pixel_getter, CoordinateToImage(columnId, rowId + 1)),
            std::apply(image_pixel_getter, CoordinateToImage(columnId, (std::ptrdiff_t)rowId - 1)),
            std::minus<float>());
    const auto square = [](float x) { return x * x; };
    float
        deltaX = FloatPixel::UnaryOperation(dx, square).Reduce(std::plus<float>()),
        deltaY = FloatPixel::UnaryOperation(dy, square).Reduce(std::plus<float>());
    return deltaX + deltaY;
}

double SeamCarver::GetPixelEnergy(size_t columnId, size_t rowId) const
{ return std::sqrt(GetPixelEnergy2(columnId, rowId)); }

SeamCarver::Seam SeamCarver::FindSeam(std::size_t parallel_size, std::size_t perpendicular_size, std::function<float(std::size_t par, std::size_t per)> getter) const
{
    assert((parallel_size * perpendicular_size) != 0); // both are not 0
    std::vector<std::vector<std::size_t>> paths(parallel_size, std::vector<std::size_t>(perpendicular_size));
    std::vector<float> dynamic_cur(perpendicular_size), dynamic_next(perpendicular_size);

    for (std::size_t y = 0; y < perpendicular_size; y++)
        dynamic_cur[y] = getter(0, y);

    for (std::size_t x = 1; x < parallel_size; x++)
    {
        for (std::size_t y = 0; y < perpendicular_size; y++)
        {
            dynamic_next[y] = getter(x, y);
            // y
            std::size_t best_i = y;
            float best_f = dynamic_cur[best_i];
            if (y > 0)
            {
                // y - 1
                const std::size_t m1 = y - 1;
                if (dynamic_cur[m1] < best_f)
                    best_i = m1, best_f = dynamic_cur[best_i];
            }
            if (y < perpendicular_size - 1)
            {
                // y + 1
                const std::size_t p1 = y + 1;
                if (dynamic_cur[p1] < best_f)
                    best_i = p1, best_f = dynamic_cur[best_i];
            }
            // update result
            dynamic_next[y] += best_f;
            paths[x][y] = best_i;
        }
        dynamic_cur.swap(dynamic_next);
    }
    auto ans_it = std::min_element(dynamic_cur.begin(), dynamic_cur.end());
    std::size_t ans_ind = ans_it - dynamic_cur.begin();

    auto ret = Seam(parallel_size);
    for (std::size_t i = 0; i < parallel_size; i++)
    {
        ret[parallel_size - i - 1] = ans_ind;
        ans_ind = paths[parallel_size - i - 1][ans_ind];
    }
    return ret;
}

SeamCarver::Seam SeamCarver::FindHorizontalSeam() const
{
    const auto [w, h] = GetImageSize();
    return FindSeam(w, h, [this](std::size_t x, std::size_t y) { return GetPixelEnergy2(x, y); });
}

SeamCarver::Seam SeamCarver::FindVerticalSeam() const
{
    const auto [w, h] = GetImageSize();
    return FindSeam(h, w, [this](std::size_t y, std::size_t x) { return GetPixelEnergy2(x, y); });
}

void SeamCarver::RemoveHorizontalSeam(const Seam& seam)
{
    const auto [w, h] = GetImageSize();
    assert(h > 0);
    assert(seam.size() == w);
    for (std::size_t x = 0; x < w - 1; x++)
    {
        std::size_t y = seam[x];
        assert(y < h);
        auto &row = m_image.m_table[x];
        row.erase(row.begin() + y);
    }
}

void SeamCarver::RemoveVerticalSeam(const Seam& seam)
{
    const auto [w, h] = GetImageSize();
    assert(w > 0);
    assert(seam.size() == h);
    for (std::size_t y = 0; y < h; y++)
        for (std::size_t x = seam[y]; x < w - 1; x++)
            m_image.m_table[x][y] = m_image.m_table[x + 1][y];
    m_image.m_table.pop_back();
}
