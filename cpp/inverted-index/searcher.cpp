
#include <cctype>
#include <iostream>
#include <cassert>
#include <sstream>

#include "searcher.h"

namespace {
template<typename T, T r, typename ...Args>
T dummyFunc(Args...) { return r; }
template<typename ...Args>
void voidDummyFunc(Args...) {}

void processStream(std::istream &strm,
        std::function<bool(const std::string &)> wordProcessor,
        std::function<bool(char, std::istream &)> special = dummyFunc<bool, false, char, std::istream &>, std::function<void(char)> verify = voidDummyFunc<char>)
{
    std::string word; // declaration here to keep capacity
    while (!strm.eof())
    {
        char peek = strm.get();
        if (special(peek, strm))
            continue;
        if (!std::isalnum(peek))
            continue;
        word = {peek};
        while (!strm.eof() && !std::isspace(peek = strm.get()))
            word.push_back(peek);
        while (word.size() && !std::isalnum(word.back()))
        {
            verify(word.back());
            word.pop_back();
        }
        if (!wordProcessor(word))
            return;
    }
}
}

void Searcher::FileContent::clear()
{
    wordsSequence.clear();
    wordPositions.clear();
}

void Searcher::add_document(const Filename & filename, std::istream & strm)
{
    assert(strm.good());
    Files::iterator file;
    if ((file = files.find(filename)) != files.end())
    {
        cleanDocument(file);
        file->second.clear();
    }
    else
        file = files.insert(files.cend(), {filename, {{}, {}}});

    processStream(strm,
        [&file, this](const std::string &word)
        {
            auto map_element = file->second.wordPositions.emplace(word, std::vector<std::size_t>()).first;
            map_element->second.push_back(file->second.wordsSequence.size());
            file->second.wordsSequence.push_back(&map_element->first);
            words2Files[word].insert(file);
            return true;
        });
}

void Searcher::cleanDocument(Files::iterator file)
{
    for (const auto &word_pair : file->second.wordPositions)
    {
        const auto &word = word_pair.first;
        auto iter = words2Files.find(word);
        iter->second.erase(file);
        if (iter->second.size() == 0)
            words2Files.erase(iter);
    }
}

void Searcher::remove_document(const Filename & filename)
{
    if (auto file = files.find(filename); file != files.end())
    {
        cleanDocument(file);
        files.erase(file);
    }
}

template<typename T, typename Func>
void filterVector(std::vector<T> &v, Func func)
{
    v.erase(std::remove_if(v.begin(), v.end(),
                [&func](const auto &arg) { return !func(arg); }),
            v.end());
}

std::pair<Searcher::DocIterator, Searcher::DocIterator> Searcher::search(const std::string & query) const
{
    bool firstFilesSelected = false;
    std::vector<Files::iterator> result_files;
    auto word_processor = [&firstFilesSelected, &result_files, this](const std::string &s)
    {
        auto it = words2Files.find(s);
        if (it == words2Files.end())
        {
            firstFilesSelected = true;
            result_files = {};
            return false;
        }
        if (!firstFilesSelected)
        {
            firstFilesSelected = true;
            result_files.assign(it->second.begin(), it->second.end());
        }
        else
            filterVector(result_files,
                         [&](const auto &a) { return it->second.find(a) != it->second.end(); });
        return result_files.size() != 0;
    };
    auto special_processor = [&](char c, std::istream &s) -> bool
    {
        if (c == '"')
        {
            std::vector<std::string> quoted_words;
            std::string word;
            char peek;
            while (!s.eof() && ((peek = s.get())) != '"')
            {
                if (peek != '"' && !std::isspace(peek))
                    word.push_back(peek);
                else
                {
                    while (word.size() && !std::isalnum(word.back()))
                        word.pop_back();
                    if (word.size() > 0)
                        quoted_words.emplace_back(std::move(word));
                }
            }
            if (word.size() > 0)
                quoted_words.emplace_back(std::move(word));
            if (s.eof())
                throw BadQuery();

            if (quoted_words.empty())
                return true;
            word_processor(quoted_words.front());
            filterVector(result_files,
                    [&quoted_words](const auto &file)
                    {
                        const auto &file_words = file->second.wordsSequence;
                        auto word_inds = file->second.wordPositions.find(quoted_words.front());
                        if (word_inds == file->second.wordPositions.end())
                            return false;
                        return std::any_of(word_inds->second.begin(), word_inds->second.end(),
                                [&quoted_words, &file_words](std::size_t sequence_start)
                                {
                                    if (sequence_start + quoted_words.size() > file_words.size())
                                        return false;
                                    return std::equal(quoted_words.begin(), quoted_words.end(),
                                            file_words.begin() + sequence_start, file_words.begin() + sequence_start + quoted_words.size(),
                                            [](const auto &l, const auto &r) { return l == *r; });
                                });
                    });
            return true;
        }
        return false;
    };

    std::stringstream strm(query);
    processStream(strm, word_processor, special_processor, [](char c) { if (c == '"') throw BadQuery(); });

    // empty query
    if (!firstFilesSelected)
        throw BadQuery();

    auto res_vec = std::make_shared<std::vector<Filename>>();
    res_vec->resize(result_files.size());
    for (std::size_t i = 0; i < result_files.size(); i++)
        (*res_vec)[i] = result_files[i]->first;
    return {DocIterator(res_vec, 0), DocIterator(res_vec, res_vec->size())};
}

/*** iterator ***/
Searcher::DocIterator::reference Searcher::DocIterator::operator*() const
{
    return answer->at(index);
}
Searcher::DocIterator::reference Searcher::DocIterator::operator[](std::size_t t) const
{
    return answer->at(index + t);
}
Searcher::DocIterator::pointer Searcher::DocIterator::operator->() const
{
    return answer->data() + index;
}
Searcher::DocIterator::difference_type Searcher::DocIterator::operator-(const DocIterator &r) const
{
    return (difference_type)index - (difference_type)r.index; // may be better to add `if` and subtract as `g - l`
}

Searcher::DocIterator & Searcher::DocIterator::operator++()
{
    index++;
    return *this;
}
Searcher::DocIterator Searcher::DocIterator::operator++(int)
{
    auto ret = *this;
    index++;
    return ret;
}

Searcher::DocIterator & Searcher::DocIterator::operator--()
{
    index--;
    return *this;
}
Searcher::DocIterator Searcher::DocIterator::operator--(int)
{
    auto ret = *this;
    index--;
    return ret;
}

bool Searcher::DocIterator::operator==(const DocIterator &r) const
{
    assert(answer == r.answer);
    return index == r.index;
}
bool Searcher::DocIterator::operator!=(const DocIterator &r) const { return !operator==(r); }


bool Searcher::DocIterator::operator< (const DocIterator &r) const
{
    assert(answer == r.answer);
    return index < r.index;
}
bool Searcher::DocIterator::operator<=(const DocIterator &r) const
{
    assert(answer == r.answer);
    return index <= r.index;
}
bool Searcher::DocIterator::operator> (const DocIterator &r) const
{
    assert(answer == r.answer);
    return index > r.index;
}
bool Searcher::DocIterator::operator>=(const DocIterator &r) const
{
    assert(answer == r.answer);
    return index >= r.index;
}

Searcher::DocIterator Searcher::DocIterator::operator+(int t)
{
	auto copy = *this;
	copy += t;
	return copy;
}
Searcher::DocIterator Searcher::DocIterator::operator-(int t)
{
	auto copy = *this;
	copy -= t;
	return copy;
}
Searcher::DocIterator & Searcher::DocIterator::operator+=(int t)
{
	index += t;
	return *this;
}
Searcher::DocIterator & Searcher::DocIterator::operator-=(int t)
{
	index -= t;
	return *this;
}