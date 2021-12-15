#include "randomized_queue.h"
#include "subset.h"

void subset(unsigned long k, std::istream & in, std::ostream & out)
{
    std::string line;
    randomized_queue<std::string> queue;
    while (std::getline(in, line))
        queue.enqueue(line);
    if (k > queue.size())
        k = queue.size();
    auto iter = queue.cbegin();
    while (k-- > 0)
    {
        out << *iter << std::endl;
        ++iter;
    }
}
