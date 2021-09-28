package info.kgeorgiy.ja.prokopenko.arrayset;

import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.NavigableSet;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.TreeSet;

public class ArraySet<T> extends AbstractSet<T> implements NavigableSet<T> {
	private final List<T> data;
	private final Comparator<? super T> comparator;
	private final Comparator<? super T> reversedComparator;

	private ArraySet(final Comparator<? super T> comparator, final Comparator<? super T> reversedComparator, final List<T> data) {
		this.comparator = comparator;
		this.reversedComparator = reversedComparator;
		this.data = data;
	}

	@SuppressWarnings("unchecked")
	public ArraySet() {
		this(null, (Comparator<? super T>)Comparator.reverseOrder(), List.of());
	}

	public ArraySet(final Collection<? extends T> collection, final Comparator<? super T> comparator) {
		this.comparator = comparator;
		if (comparator == null) {
			@SuppressWarnings("unchecked")
			Comparator<? super T> temp = (Comparator<? super T>)Comparator.reverseOrder();
			this.reversedComparator = temp;
		} else {
			this.reversedComparator = comparator.reversed();
		}

		if (collection != null) {
			var sorted = new TreeSet<T>(comparator);
			sorted.addAll(collection);
			this.data = Collections.unmodifiableList(new ArrayList<T>(sorted));
		} else {
			this.data = List.of();
		}
	}
	public ArraySet(final Comparator<? super T> comparator) {
		this(null, comparator);
	}
	public ArraySet(final Collection<? extends T> collection) {
		this(collection, null);
	}

	private int compare(T a, T b) {
		a = Objects.requireNonNull(a);
		b = Objects.requireNonNull(b);
		if (comparator != null) {
			return comparator.compare(a, b);
		}
		@SuppressWarnings("unchecked")
		Comparable<? super T> ac = (Comparable<? super T>)a;
		return ac.compareTo(b);
	}

	@Override
	public Comparator<? super T> comparator() {
		return comparator;
	}

	@Override
	public int size() {
		return data.size();
	}

	private boolean indexIn(final int i) {
		return i >= 0 && i < size();
	}
	private T get(final int index) {
		if (!indexIn(index)) {
			throw new NoSuchElementException();
		}
		return data.get(index);
	}
	@Override
	public T first() {
		return get(0);
	}
	@Override
	public T last() {
		return get(size() - 1);
	}

	private NavigableSet<T> subSetInd(final int from, final int to) {
		return new ArraySet<T>(comparator, reversedComparator, data.subList(from, to));
	}

	private int searchBound(final T a, final int diffPos, final int diffNeg) {
		if (isEmpty()) {
			return 0;
		}
		int res = Collections.binarySearch(data, a, comparator);
		return res < 0 ? -res - 1 + diffNeg : res + diffPos;
	}
	private int lowerBound(final T from) {
		return searchBound(from, -1, -1);
	}
	private int floorBound(final T from) {
		return searchBound(from, 0, -1);
	}
	private int higherBound(final T to) {
		return searchBound(to, 1, 0);
	}
	private int ceilingBound(final T from) {
		return searchBound(from, 0, 0);
	}

	@Override
	public NavigableSet<T> tailSet(final T fromElement, final boolean inclusive) {
		if (inclusive) {
			return subSetInd(ceilingBound(fromElement), size());
		} else {
			return subSetInd(higherBound(fromElement), size());
		}
	}
	@Override
	public NavigableSet<T> headSet(final T toElement, final boolean inclusive) {
		if (inclusive) {
			return subSetInd(0, higherBound(toElement));
		} else {
			return subSetInd(0, ceilingBound(toElement));
		}
	}

	@Override
	public NavigableSet<T> tailSet(final T fromElement) {
		return tailSet(fromElement, true);
	}
	@Override
	public NavigableSet<T> headSet(final T toElement) {
		return headSet(toElement, false);
	}

	@Override
	public NavigableSet<T> subSet(final T fromElement, final T toElement) {
		return subSet(fromElement, true, toElement, false);
	}
	@Override
	public NavigableSet<T> subSet(final T fromElement, final boolean fromInclusive,
	                              final T toElement, final boolean toInclusive) {
		int compared = compare(fromElement, toElement);
		if (compared > 0) {
			throw new IllegalArgumentException("invalid range");
		}
		if (compared == 0 && !(fromInclusive && toInclusive)) {
			return new ArraySet<T>(comparator, reversedComparator, List.of());
		}
		int from = fromInclusive ? ceilingBound(fromElement) : higherBound(fromElement);
		int to = toInclusive ? higherBound(toElement) : ceilingBound(toElement);
		return subSetInd(from, to);
	}

	@Override
	public Iterator<T> iterator() {
		return data.iterator();
	}
	@Override
	public Iterator<T> descendingIterator() {
		return data.listIterator(size());
	}

	@Override
	public NavigableSet<T> descendingSet() {
		return new ArraySet<T>(reversedComparator, comparator, ReverseListView.reversedView(data));
	}

	@Override
	public T pollLast() {
		throw new UnsupportedOperationException("pollLast");
	}
	@Override
	public T pollFirst() {
		throw new UnsupportedOperationException("pollFirst");
	}

	private T inBoundsOrNull(final int i) {
		if (!indexIn(i)) {
			return null;
		}
		return data.get(i);
	}

	@Override
	public T higher(final T a) {
		return inBoundsOrNull(higherBound(a));
	}

	@Override
	public T ceiling(final T a) {
		return inBoundsOrNull(ceilingBound(a));
	}

	@Override
	public T lower(final T a) {
		return inBoundsOrNull(lowerBound(a));
	}

	@Override
	public T floor(final T a) {
		return inBoundsOrNull(floorBound(a));
	}

	@Override
	public boolean contains(final Object o) {
		if (isEmpty()) {
			return false;
		}
		// how to use wildcard type from Comparator<? super T>
		@SuppressWarnings("unchecked")
		T t = (T)o;
		int i = searchBound(t, 0, -size() - 4);
		return indexIn(i);
	}
}

