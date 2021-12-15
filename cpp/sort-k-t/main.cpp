/* Coding style:
 * Classes, functions, UpperCamel
 * locals - snake
 */

#include <iostream>
#include <algorithm>
#include <vector>
#include <string>
#include <tuple>
#include <cstring>
#include <fstream>

namespace {
class LineHandler
{
public:
    std::string str;
    std::vector<std::pair<std::size_t, std::size_t>> values;
    LineHandler() = default;
    LineHandler(LineHandler &&) = default;
    LineHandler & operator=(LineHandler &&) = default;
    std::string Get(std::size_t ind) const
    {
        if (ind >= values.size())
            return "";
        return str.substr(values[ind].first, values[ind].second);
    }
};

bool CStrEq(const char *str1, const char * str2) { return strcmp(str1, str2) == 0; }
bool ParamIsK(const char *str) { return CStrEq(str, "-k"); }
bool ParamIsT(const char *str) { return CStrEq(str, "-t"); }

using SeparatorWorkFunction = std::size_t (*)(const std::string &str, const std::string &sep, std::size_t start);

class FunctionsWithWS
{
public:
    static std::size_t Find(const std::string &str, [[maybe_unused]] const std::string &sep, std::size_t start)
    {
        for (std::size_t i = start; i < str.size(); i++)
            if (std::isspace(str[i]))
                return i;
        return std::string::npos;
    }
    static std::size_t Skip(const std::string &str, [[maybe_unused]] const std::string &sep, std::size_t start)
    {
        for (std::size_t i = start; i < str.size(); i++)
            if (!std::iswspace(str[i]))
                return i;
        return str.size();
    }
};

class FunctionsWithSep
{
public:
    static std::size_t Find(const std::string &str, const std::string &sep, std::size_t start)
    {
        return str.find(sep, start);
    }
    static std::size_t Skip([[maybe_unused]] const std::string &str, const std::string &sep, std::size_t start)
    {
        return start + sep.length();
    }
};

template<typename FunctionClass>
std::vector<LineHandler> ReadLines(const std::string &file_name, const std::string &separator)
{
    // read file line by line
    std::vector<LineHandler> lines;
    std::ifstream _file_stream;
    // is it better to make a pointer and only 1 comparision?
    if (!file_name.empty())
    {
        _file_stream.open(file_name);
        if (!_file_stream.is_open())
            throw std::invalid_argument("Can't open file");
    }
    std::istream &in = file_name.empty() ? std::cin : _file_stream;
    std::string line;
    // class with functions
    while (std::getline(in, line))
    {
        // emplace_back forwards arguments to the constructor => no additional copy in debug (idk about release)
        lines.emplace_back();
        std::size_t pos, last_pos = 0;
        while ((pos = FunctionClass::Find(line, separator, last_pos)) != std::string::npos)
        {
            lines.back().values.emplace_back(last_pos, pos - last_pos);
            last_pos = FunctionClass::Skip(line, separator, pos);
        }
        lines.back().values.emplace_back(last_pos, line.length() - last_pos);
        lines.back().str.swap(line);
    }
    return lines;
}
}

int main(int argc, char * argv[])
{
    std::vector<std::size_t> keys;
    std::string separator;
    // parse arguments
    std::string filename;
    std::size_t start_ind = 1;
    if (argc >= 2 && !ParamIsT(argv[1]) && !ParamIsK(argv[1]) && !CStrEq(argv[1], "-"))
    {
        filename = argv[1];
        start_ind = 2;
    }
    for (int i = start_ind; i < argc; i++)
        if (ParamIsK(argv[i]))
        {
            i++;
            while (i < argc && !ParamIsT(argv[i]))
            {
                std::size_t kv;
                try
                {
                    kv = std::stoul(argv[i]);
                }
                catch (...)
                {
                    std::cerr << "Can't parse value of key" << std::endl;
                    return 1;
                }
                if (kv == 0)
                {
                    std::cerr << "Numeration from 1 is used for keys" << std::endl;
                    return 1;
                }
                keys.push_back(kv - 1);
                i++;
            }
            i--;
        }
        else if (ParamIsT(argv[i]))
        {
            i++;
            if (i >= argc)
            {
                std::cerr << "Wrong arguments. Expected `-t SEPARATOR`" << std::endl;
                return 1;
            }
            separator = argv[i];
        }
        else
        {
            std::cerr << "Wrong parameter" << std::endl;
            return 1;
        }

     auto lines = separator.empty()
             ?  ReadLines<FunctionsWithWS >(filename, separator)
             :  ReadLines<FunctionsWithSep>(filename, separator);

    // sort
    if (keys.empty())
        std::sort(lines.begin(), lines.end(), [](const LineHandler &l, const LineHandler &r) -> bool { return l.str < r.str; });
    else
        std::sort(lines.begin(), lines.end(),
            [&](const LineHandler &l, const LineHandler &r) -> bool
            {
                for (const auto &a : keys)
                    if (int cres = l.Get(a).compare(r.Get(a)); cres < 0)
                        return true;
                    else if (cres > 0)
                        return false;
                return false;
            });
    for (const auto &a : lines)
        std::cout << a.str << std::endl;
    return 0;
}
