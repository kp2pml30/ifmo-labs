package info.kgeorgiy.ja.prokopenko.arrayset;

import java.util.AbstractList;
import java.util.List;
import java.util.Objects;

public class ReverseListView<T> extends AbstractList<T> {
	private List<T> lst;

	private ReverseListView(final List<T> lst) {
		this.lst = Objects.requireNonNull(lst);
	}

	@Override
	public T get(final int i) {
		return lst.get(size() - 1 - i);
	}

	@Override
	public int size() {
		return lst.size();
	}

	public static <T> List<T> reversedView(final List<T> lst) {
		if (lst instanceof ReverseListView) {
			return ((ReverseListView<T>)lst).lst;
		} else {
			return new ReverseListView<T>(lst);
		}
	}
}

