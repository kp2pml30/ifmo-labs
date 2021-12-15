#include <cassert>
#include "Image.h"

Image::Image(std::vector<std::vector<Image::Pixel>> table)
    : m_table(std::move(table))
{}

Image::Pixel::Pixel(int red, int green, int blue)
    : m_red(red)
    , m_green(green)
    , m_blue(blue)
{}

std::size_t Image::GetHeight() const
{
    if (GetWidth() == 0)
        return 0;
    return m_table.front().size();
}
std::size_t Image::GetWidth() const
{ return m_table.size(); }

Image::Pixel Image::GetPixel(size_t columnId, size_t rowId) const
{
    assert(columnId < GetWidth() && rowId < GetHeight());
    return m_table[columnId][rowId];
}
