#include "allocator.h"
#include "cache.h"

#include <iostream>
#include <string>

namespace {

struct StringKey : public std::string
{
    virtual ~StringKey() = default;
    StringKey(const std::string &r) : std::string(r) {}
    StringKey(std::string &&r) : std::string(r) {}

    using std::string::string;
    bool operator==(const StringKey &k) const
    { return *static_cast<const std::string *>(this) == static_cast<const std::string &>(k); }
};

struct String : public StringKey
{
    bool marked = false;

    String(const StringKey & key)
        : StringKey(key)
    {}

    bool operator == (const StringKey & k) const
    { return StringKey::operator==(k); }

    friend std::ostream & operator << (std::ostream & strm, const String & str)
    { return strm << static_cast<StringKey>(str); }
};

using TestCache = Cache<StringKey, String, AllocatorWithPool>;

} // anonymous namespace

int main()
{
    TestCache cache(9, 18, std::initializer_list<std::size_t>{sizeof(String)});
    std::string line;
    while (std::getline(std::cin, line)) {
        auto & s = cache.get<String>(line);
        if (s.marked) {
            std::cout << "known" << std::endl;
        }
        s.marked = true;
    }
    std::cout << "\n" << cache << std::endl;
}
