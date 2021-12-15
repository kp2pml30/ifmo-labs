#pragma once

#include <set>
#include <map>
#include <string>
#include <vector>
#include <utility>
#include <memory>
#include <functional>

class Searcher
{
public:
    using Filename = std::string; // or std::filesystem::path

    // index modification
    void add_document(const Filename & filename, std::istream & strm);

    void remove_document(const Filename & filename);

    // queries
    class DocIterator
    {
    private:
        friend Searcher;
        std::shared_ptr<std::vector<Filename>> answer;
        std::size_t index;
        DocIterator(const std::shared_ptr<std::vector<Filename>> &answer, std::size_t index) : answer(answer), index(index) {}
    public:
        using difference_type = std::ptrdiff_t ;
        using iterator_category = std::random_access_iterator_tag;
        using value_type = const Filename;
        using pointer    = const value_type *;
        using reference  = const value_type &;

        reference operator*() const;
        reference operator[](std::size_t t) const;
        pointer operator->() const;

        difference_type operator-(const DocIterator &r) const;

        DocIterator & operator++();
        DocIterator operator++(int);
        DocIterator & operator--();
        DocIterator operator--(int);

        bool operator==(const DocIterator &r) const;
        bool operator!=(const DocIterator &r) const;
	bool operator< (const DocIterator &r) const;
	bool operator<=(const DocIterator &r) const;
	bool operator> (const DocIterator &r) const;
	bool operator>=(const DocIterator &r) const;

	DocIterator operator+(int t);
	DocIterator operator-(int t);
	DocIterator & operator+=(int t);
	DocIterator & operator-=(int t);
    };

    class BadQuery : public std::exception
    {
        // inherit constructors
        using std::exception::exception;
    };

    std::pair<DocIterator, DocIterator> search(const std::string & query) const;
private:
    template<typename T>
    struct PointerComparator
    {
        bool operator()(const T *l, const T *r) const { return *l < *r; }
    };

    class FileContent
    {
    public:
        std::vector<const std::string *> wordsSequence;
        std::map<std::string, std::vector<std::size_t>> wordPositions;
        void clear();
    };

    using Files = std::map<Filename, FileContent>;
    class FilesIteratorComparator
    {
    public:
        bool operator()(const Files::iterator &l, const Files::iterator &r) const { return l->first < r->first; }
    };

    using WordsToFiles = std::map<std::string, std::set<Files::iterator, FilesIteratorComparator>>;

    Files files; // filename -> {set of words, words order (points on string from set)}
    WordsToFiles words2Files; // word -> filename -> entries_of_word (sorted)

    void cleanDocument(Files::iterator what);
};
