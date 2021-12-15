#pragma once

// #define RBTREE_ONLY // test debugger

#include <map>
#include <set>
#include <optional>
#include <iostream>
#include <memory>
#include <cassert>

class Point {
private:
    double _x, _y;

    int spaceshipOperator(const Point &r) const;
public:
    Point() {}
    explicit Point(double xy);
	Point(double x, double y);

	double x() const;
	double y() const;
    double distance2(const Point &) const;
	double distance(const Point &) const;

	bool operator< (const Point &) const;
	bool operator> (const Point &) const;
	bool operator<= (const Point &) const;
	bool operator>= (const Point &) const;
	bool operator== (const Point &) const;
	bool operator!= (const Point &) const;

	friend std::ostream & operator << (std::ostream &, const Point &);
};

class Rect {
private:
    double _xmin, _xmax, _ymin, _ymax;
public:
	Rect(const Point & left_bottom, const Point & right_top);

	double xmin() const;
	double ymin() const;
	double xmax() const;
	double ymax() const;
	Point lb() const;
	Point rt() const;
    double distance2(const Point & p) const;
	double distance(const Point & p) const;

	bool contains(const Point & p) const;
	bool intersects(const Rect &) const;
};

template<typename T>
class shared_vector {
private:
    std::shared_ptr<T[]> d;
    std::size_t last = 0, cap;
    void extend() {
        std::shared_ptr<T[]> dn(new T[cap * 2]);
        for (std::size_t i = 0; i < last; i++)
            dn[i] = d[i];
        cap *= 2;
        d = dn;
    }
public:
    shared_vector(std::size_t initial_capacity = 1) : d(std::shared_ptr<T[]>(new T[initial_capacity])), cap(initial_capacity) { assert(cap != 0); }

    T & operator[](std::size_t ind) { return d[ind]; }
    const T & operator[](std::size_t ind) const { return d[ind]; }

    std::shared_ptr<T[]> data() const { return d; }
    std::size_t size() const { return last; }

    void push(const T &w) {
        if (last == cap)
            extend();
        d[last++] = w;
    }
};


namespace pointtree {
class SharedPointArrIterator {
private:
    std::shared_ptr<Point[]> ptr;
    std::size_t ind;
public:
    using iterator_category = std::random_access_iterator_tag;
    using value_type = const Point;
    using difference_type = std::int64_t;
    using pointer = const value_type * ;
    using reference = const value_type & ;

    SharedPointArrIterator(std::shared_ptr<Point[]> ptr, std::size_t ind) : ptr(ptr), ind(ind) {}

    pointer operator-> () const;
    reference operator* () const;
    reference operator[] (std::size_t ind) const;

    bool operator== (const SharedPointArrIterator &) const;
    bool operator!= (const SharedPointArrIterator &) const;

    SharedPointArrIterator operator++ ();
    SharedPointArrIterator operator++ (int);
    SharedPointArrIterator operator+ (std::size_t off) const;
    SharedPointArrIterator & operator+= (std::size_t off);

    std::int64_t operator- (const SharedPointArrIterator &r) const;
};
}

namespace rbtree {

class PointSet {
private:
    std::map<double, std::set<double>> pts;
    shared_vector<Point> all;
public:
    using ForwardIt = pointtree::SharedPointArrIterator;
    PointSet();

    bool empty() const;
    std::size_t size() const;
    void put(const Point &);
    PointSet & operator<< (const Point &p) { put(p); return *this; }
    bool contains(const Point &) const;

    std::pair<ForwardIt, ForwardIt> range(const Rect &) const;

    ForwardIt begin() const;
    ForwardIt end() const;

    std::optional<Point> nearest(const Point &) const;

    std::pair<ForwardIt, ForwardIt> nearest(const Point & p, std::size_t k) const;

    friend std::ostream & operator << (std::ostream &, const PointSet &);
};

}

namespace kdtree {
class KdRangeSearchPerformer;
class KdKNNSearchPerformer;

#ifndef RBTREE_ONLY
class PointSet {
private:
    friend KdRangeSearchPerformer;
    friend KdKNNSearchPerformer;
    class Node {
    public:
        friend PointSet;
        Node *left = nullptr, *right = nullptr;
        Point data;

        Node(const Point & data);

        ~Node();
    };
    Node *root = nullptr;
    shared_vector<Point> all;
public:

    using ForwardIt = pointtree::SharedPointArrIterator;

    PointSet();
    PointSet(const PointSet &) = delete;
    PointSet(PointSet &&) = delete;
    void operator=(const PointSet &) = delete;
    void operator=(PointSet &&) = delete;
    ~PointSet();

    bool empty() const;
    std::size_t size() const;
    void put(const Point &);
    bool contains(const Point &) const;

    std::pair<ForwardIt, ForwardIt> range(const Rect &) const;
    ForwardIt begin() const;
    ForwardIt end() const;

    std::optional<Point> nearest(const Point &) const;
    std::pair<ForwardIt, ForwardIt> nearest(const Point & p, std::size_t k) const;

    friend std::ostream & operator << (std::ostream &, const PointSet &);
};
#else
using rbtree::PointSet;
#endif
}
