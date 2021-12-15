#pragma once

#include <tuple>
#include <functional>

#include "Image.h"

class SeamCarver
{
    using Seam = std::vector<size_t>;

public:
    SeamCarver(Image image);

    /**
     * Returns current image
     */
    const Image& GetImage() const;

    /**
     * Gets current image width
     */
    size_t GetImageWidth() const;

    /**
     * Gets current image height
     */
    size_t GetImageHeight() const;

    /**
     * Get image size
     * @return {w, h}
     */
    std::tuple<std::size_t, std::size_t> GetImageSize() const;

    /**
     * Get pixel from current image
     * @param columnId column index (x)
     * @param rowId row index (y)
     */
    Image::Pixel GetImagePixel(std::size_t columnId, std::size_t rowId) const;

    /**
     * Get coordinates moved to picture
     * @param columnId column index (x)
     * @param rowId row index (y)
     */
     std::tuple<std::size_t, std::size_t> CoordinateToImage(std::ptrdiff_t columnId, std::ptrdiff_t rowId) const;

    /**
     * Returns pixel energy square `(pow(energy, 2))`
     * @param columnId column index (x)
     * @param rowId row index (y)
     */
    double GetPixelEnergy2(size_t columnId, size_t rowId) const;

    /**
     * Returns pixel energy
     * @param columnId column index (x)
     * @param rowId row index (y)
     */
    double GetPixelEnergy(size_t columnId, size_t rowId) const;

    /**
     * Returns sequence of pixel row indexes (y)
     * (x indexes are [0:W-1])
     */
    Seam FindHorizontalSeam() const;

    /**
     * Returns sequence of pixel column indexes (x)
     * (y indexes are [0:H-1])
     */
    Seam FindVerticalSeam() const;

    /**
     * Removes sequence of pixels from the image
     */
    void RemoveHorizontalSeam(const Seam& seam);

    /**
     * Removes sequence of pixes from the image
     */
    void RemoveVerticalSeam(const Seam& seam);

private:
    Image m_image;

    Seam FindSeam(std::size_t parallel_size, std::size_t perpendicular_size, std::function<float(std::size_t per,std::size_t pat)> getter) const;
};