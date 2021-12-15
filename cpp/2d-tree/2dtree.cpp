#include <cmath>
#include <cstring>
#include <vector>
#include <cassert>
#include <algorithm>
#include <functional>
#include <numeric>

#include "primitives.h"

/*** ostream operators ***/
std::ostream & operator<<(std::ostream &s, const Point &r) {
    s << '{' << r.x() << "; " << r.y() << '}';
    return s;
}
std::ostream & operator<<(std::ostream &s, const Rect &r) {
    s << '[' << r.lb() << "; " << r.rt() << ']';
    return s;
}

/*** Point ***/
Point::Point(double xy) : _x(xy), _y(xy) {}
Point::Point(double x, double y) : _x(x), _y(y) {}
int Point::spaceshipOperator(const Point &r) const {
    return std::memcmp(&_x, &r._x, sizeof(double) * 2);
}
double Point::x(void) const { return _x; }
double Point::y(void) const { return _y; }
double Point::distance2(const Point &r) const { double dx = r.x() - x(), dy = r.y() - y(); return dx * dx + dy * dy; }
double Point::distance(const Point &r) const { return std::sqrt(distance2(r)); }
bool Point::operator< (const Point &r) const { return spaceshipOperator(r) < 0; }
bool Point::operator> (const Point &r) const { return spaceshipOperator(r) > 0; }
bool Point::operator<= (const Point &r) const { return spaceshipOperator(r) <= 0; }
bool Point::operator>= (const Point &r) const { return spaceshipOperator(r) >= 0; }
bool Point::operator== (const Point &r) const {
    return x() == r.x() && y() == r.y();
}
bool Point::operator!= (const Point &r) const {
    return !operator== (r);
}

/*** Rect ***/
Rect::Rect(const Point & lb, const Point & rt) : _xmin(lb.x()), _xmax(rt.x()), _ymin(lb.y()), _ymax(rt.y()) {
    assert(lb.x() <= rt.x() && lb.y() <= rt.y());
}

double Rect::xmin(void) const { return _xmin; }
double Rect::ymin(void) const { return _ymin; }
double Rect::xmax(void) const { return _xmax; }
double Rect::ymax(void) const { return _ymax; }
Point Rect::lb(void) const { return Point(_xmin, _ymin); }
Point Rect::rt(void) const { return Point(_xmax, _ymax); }
double Rect::distance2(const Point & p) const {
    return p.distance2(
            Point(std::min(xmax(), std::max(xmin(), p.x())),
                  std::min(ymax(), std::max(ymin(), p.y())))
            );
}
double Rect::distance(const Point & p) const { return std::sqrt(distance2(p)); }
bool Rect::contains(const Point & p) const {
    return p.x() >= xmin() && p.x() <= xmax() && p.y() >= ymin() && p.y() <= ymax();
}
bool Rect::intersects(const Rect & r) const {
    return !(xmin() >= r.xmax() || xmax() <= r.xmin()
          || ymin() >= r.ymax() || ymax() <= r.ymin());
}

/*** iterator ***/
pointtree::SharedPointArrIterator::pointer pointtree::SharedPointArrIterator::operator-> (void) const {
    return ptr.get() + ind;
}
pointtree::SharedPointArrIterator::reference pointtree::SharedPointArrIterator::operator* (void) const {
    return ptr[ind];
}
pointtree::SharedPointArrIterator::reference pointtree::SharedPointArrIterator::operator[] (std::size_t ind) const {
    return ptr[this->ind + ind];
}

pointtree::SharedPointArrIterator pointtree::SharedPointArrIterator::operator++ (void) {
    ind++;
    return *this;
}
pointtree::SharedPointArrIterator pointtree::SharedPointArrIterator::operator++ (int) {
    auto ret = *this;
    ind++;
    return ret;
}
pointtree::SharedPointArrIterator pointtree::SharedPointArrIterator::operator+ (std::size_t off) const {
    return SharedPointArrIterator(ptr, ind + off);
}
pointtree::SharedPointArrIterator & pointtree::SharedPointArrIterator::operator+= (std::size_t off) {
    ind += off;
    return *this;
}

bool pointtree::SharedPointArrIterator::operator== (const pointtree::SharedPointArrIterator &r) const {
    assert(ptr == r.ptr);
    return ind == r.ind;
}
bool pointtree::SharedPointArrIterator::operator!= (const pointtree::SharedPointArrIterator &r) const { return !operator== (r); }
std::int64_t pointtree::SharedPointArrIterator::operator- (const SharedPointArrIterator &r) const {
    assert(ptr == r.ptr);
    if (ind >= r.ind)
        return (std::int64_t)(ind - r.ind);
    return -(std::int64_t)(r.ind - ind);
}

/*** trees ***/

namespace rbtree {
PointSet::PointSet(void) {}

bool PointSet::empty() const { return size() == 0; }
std::size_t PointSet::size() const { return all.size(); }
void PointSet::put(const Point &p) {
    if (pts[p.x()].insert(p.y()).second)
        all.push(p);
}
bool PointSet::contains(const Point &p) const {
    auto iter = pts.find(p.x());
    return iter != pts.cend() && iter->second.find(p.y()) != iter->second.cend();
}

std::pair<PointSet::ForwardIt, PointSet::ForwardIt> PointSet::range(const Rect &p) const {
    shared_vector<Point> ret;
    for (auto x = pts.lower_bound(p.xmin()), xlast = pts.upper_bound(p.xmax()); x != xlast; ++x)
        for (auto y = x->second.lower_bound(p.ymin()), ylast = x->second.upper_bound(p.ymax()); y != ylast; ++y)
            ret.push(Point(x->first, *y));
    return {ForwardIt(ret.data(), 0), ForwardIt(ret.data(), ret.size())};
}
PointSet::ForwardIt PointSet::PointSet::begin(void) const {
    return ForwardIt(all.data(), 0);
}
PointSet::ForwardIt PointSet::end(void) const {
    return ForwardIt(all.data(), size());
}

std::optional<Point> PointSet::nearest(const Point & p) const {
    if (empty())
        return {};
    return *std::min_element(begin(), end(), [&p](const Point & p1, const Point & p2) -> bool { return p.distance2(p1) < p.distance2(p2); });
}

std::pair<PointSet::ForwardIt, PointSet::ForwardIt> PointSet::nearest(const Point & p, std::size_t k) const {
    k = std::min(size(), k);
    // multimap
    std::map<double, std::vector<Point>> result;
    for (auto &x : pts)
        for (auto &y : x.second) {
            const Point cur(x.first, y);
            result[p.distance2(cur)].push_back(cur);
        }
    std::size_t ind = 0;
    std::shared_ptr<Point[]> res(new Point[k]);
    for (auto &vec : result) {
        if (ind >= k)
            break;
        auto &from = vec.second;
        std::size_t to = std::min(k - ind, from.size());
        std::copy(from.data(), from.data() + to, res.get() + ind);
        ind += to;
    }

    return {ForwardIt(res, 0), ForwardIt(res, k)};
}
}

#ifndef RBTREE_ONLY
namespace kdtree {
PointSet::Node::Node(const Point & data) : data(data) {}
PointSet::Node::~Node() {
    if (left  != nullptr) delete left;
    if (right != nullptr) delete right;
}

static double XGetter(const Point &p) { return p.x(); }
static double YGetter(const Point &p) { return p.y(); }

PointSet::PointSet() {}
PointSet::~PointSet() {
    if (root != nullptr) delete root;
}

bool PointSet::empty() const { return size() == 0; }
std::size_t PointSet::size() const { return all.size(); }
void PointSet::put(const Point & p) {
    if (root == nullptr) {
        all.push(p);
        root = new Node(p);
        return;
    }
    auto cur = root;
    auto coord_func = [&](auto getter) -> bool {
        if (p == cur->data) {
            return true;
        }
        auto setter = [&](Node * Node::*ptrToChild) -> bool {
            if (cur->*ptrToChild == nullptr) {
                all.push(p);
                cur->*ptrToChild = new Node(p);
                return true;
            } else {
                cur = cur->*ptrToChild;
            }
            return false;
        };
        if (getter(p) >= getter(cur->data)) {
            if (setter(&Node::right))
                return true;
        } else {
            if (setter(&Node::left))
                return true;
        }
        return false;
    };
    while (true) {
        if (coord_func(XGetter))
            break;
        if (coord_func(YGetter))
            break;
    }
}

bool PointSet::contains(const Point & p) const {
    auto cur = root;
    auto coord_func = [&](auto getter, auto cogetter) -> bool {
        if (const auto d = getter(cur->data); d < getter(p))
            cur = cur->right;
        else if (d == getter(p) && cogetter(cur->data) == cogetter(p))
            return true;
        else
            cur = cur->left;
        return false;
    };
    while (cur != nullptr) {
        if (coord_func(XGetter, YGetter))
            return true;
        if (cur == nullptr)
            break;
        if (coord_func(YGetter, XGetter))
            return true;
    }
    return false;
}

[[maybe_unused]] static Rect GetInfiniteRect(void) {
    return Rect(Point(-std::numeric_limits<double>::infinity()), Point(+std::numeric_limits<double>::infinity()));
}
class KdRangeSearchPerformer {
public:
    shared_vector<Point> result; // `this` may be passed via register => no recursion overload
    Rect bounds;

    KdRangeSearchPerformer(const Rect &bounds) : bounds(bounds) {}

    void KdSearch(PointSet::Node *node, bool isEven = true) {
        if (node == nullptr)
            return;
        std::function<double(const Point &p)> getter, cogetter;
        if (isEven)
            getter = XGetter, cogetter = YGetter;
        else
            getter = YGetter, cogetter = XGetter;
        if (bounds.contains(node->data))
            result.push(node->data);
        if (getter(bounds.lb()) < getter(node->data))
            KdSearch(node->left, isEven ^ 1);
        if (getter(bounds.rt()) >= getter(node->data))
            KdSearch(node->right, isEven ^ 1);
    }

    void IncludeAll(PointSet::Node *node) {
        while (true) {
            if (node == nullptr)
                return;
            IncludeAll(node->left);
            result.push(node->data);
            node = node->right;
        }
    }
};

class KdKNNSearchPerformer {
public:
    std::multimap<double, Point> result;
    Point pivot;
    std::size_t k;
    KdKNNSearchPerformer(const Point &pt, std::size_t k) : pivot(pt), k(k) {}

    void KNN(PointSet::Node *node, bool isEven = true) {
        if (node == nullptr) {
            return;
        }
        auto getter = isEven ? XGetter : YGetter;
        auto pcoord = getter(pivot), ncoord = getter(node->data);
        PointSet::Node *f, *l;
        if (pcoord >= ncoord)
            f = node->right, l = node->left;
        else
            f = node->left, l = node->right;
        KNN(f, isEven ^ 1);
        result.insert({pivot.distance2(node->data), node->data});
        if (result.size() < k || pow(pcoord - ncoord, 2) <= std::prev(result.end())->first)
            KNN(l, isEven ^ 1);
    }

    double NNbd2 = std::numeric_limits<double>::infinity();
    Point NNbest;

    void NN(PointSet::Node *node, bool isEven = true) {
        if (node == nullptr) {
            return;
        }
        std::function<double(const Point &p)> getter, cogetter;
        if (isEven)
            getter = XGetter, cogetter = YGetter;
        else
            getter = YGetter, cogetter = XGetter;
        auto pcoord = getter(pivot), ncoord = getter(node->data);
        double d2 = pivot.distance2(node->data);
        if (d2 < NNbd2)
            NNbd2 = d2, NNbest = node->data;
        PointSet::Node *f, *l;
        if (getter(pivot) >= getter(node->data))
            f = node->right, l = node->left;
        else
            f = node->left, l = node->right;
        NN(f, isEven ^ 1);
        if (pow(pcoord - ncoord, 2) <= NNbd2)
            NN(l, isEven ^ 1);
    }
};

std::pair<PointSet::ForwardIt, PointSet::ForwardIt> PointSet::range(const Rect & r) const {
    KdRangeSearchPerformer searcher(r);
    searcher.KdSearch(root);
    auto &result = searcher.result;
    auto *result_data_ptr = result.data().get();
    std::sort(result_data_ptr, result_data_ptr + result.size(), [](const Point &p1, const Point &p2) -> bool { return p1.x() < p2.x() || (p1.x() == p2.x() && p1.y() < p2.y()); });
    return {ForwardIt(result.data(), 0), ForwardIt(result.data(), result.size())};
}

PointSet::ForwardIt PointSet::begin(void) const {
    return ForwardIt(all.data(), 0);
}
PointSet::ForwardIt PointSet::end(void) const {
    return ForwardIt(all.data(), size());
}

std::optional<Point> PointSet::nearest(const Point & p) const {
    if (empty()) return {};
    KdKNNSearchPerformer performer(p, 1);
    performer.NN(root);
    return {performer.NNbest};
}
std::pair<PointSet::ForwardIt, PointSet::ForwardIt> PointSet::nearest(const Point & p, std::size_t k) const {
        KdKNNSearchPerformer performer(p, k);
        performer.KNN(root);
        shared_vector<Point> res;
        for (auto &a : performer.result)
            if (res.size() >= k)
                break;
            else
                res.push(a.second);
        return {ForwardIt(res.data(), 0), ForwardIt(res.data(), res.size())};
}
}
#endif
