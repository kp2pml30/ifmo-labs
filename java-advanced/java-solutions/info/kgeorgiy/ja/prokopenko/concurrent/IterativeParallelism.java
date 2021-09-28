package info.kgeorgiy.ja.prokopenko.concurrent;

import info.kgeorgiy.java.advanced.concurrent.ListIP;

import info.kgeorgiy.java.advanced.mapper.ParallelMapper;

import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.Collection;
import java.util.function.Predicate;
import java.util.function.Function;
import java.util.function.Supplier;

public class IterativeParallelism implements ListIP {
	private final ParallelMapper mapper;

	public IterativeParallelism(final ParallelMapper mapper) {
		if (mapper == null) {
			throw new NullPointerException("mapper is null");
		}
		this.mapper = mapper;
	}
	public IterativeParallelism() {
		this.mapper = new DynamicMapper();
	}

	private <T, H> List<H> listStart(int threads,
			final List<? extends T> list,
			final Function<List<? extends T>, H> func) throws InterruptedException {
		if (list.isEmpty()) {
			return List.of();
		}
		threads = Math.max(1, Math.min(list.size(), threads));

		List<List<? extends T>> args = new ArrayList<>();

		final int avgLen = list.size() / threads;
		int reminder = list.size() - avgLen * threads;

		int start = 0;
		for (int i = 0; i < threads; i++) {
			final int len = avgLen + (reminder > 0 ? 1 : 0);
			reminder--;
			args.add(list.subList(start, start + len));
			start += len;
		}
		return mapper.map(func, args);
	}

	//*
	@Override
	public <T> T maximum(int i,
			final List<? extends T> list,
			final Comparator<? super T> comparator) throws InterruptedException {
		// get === orElseThrow
		List<T> result = listStart(i, list, (List<? extends T> lst) -> lst.stream().max(comparator).orElseThrow());
		return result.stream().max(comparator).orElseThrow();
	}
	/*/
	// this maximum is way better for sleep: it makes time = log when possible, however
	// sleep performance says "too slow" on 0.4 ratio which is
	//     5|2|2|1 = 4*100 --- log_2 reduce
	//   against
	//     1|1|...|1 = 10*100` --- simple division = no parallelism
	@Override
	public <T> T maximum(int i,
			List<? extends T> list,
			final Comparator<? super T> comparator) throws InterruptedException {
		Function<List<? extends T>, T> maximizer = (List<? extends T> lst) -> lst.stream().max(comparator).get();
		while (list.size() > 2) {
			list = listStart(Math.min(i, list.size() / 2), list, maximizer);
		}
		return maximizer.apply(list);
	}
	//*/

	@Override
	public <T> T minimum(final int i,
			final List<? extends T> list,
			final Comparator<? super T> comparator) throws InterruptedException {
		return maximum(i, list, comparator.reversed());
	}

	//*
	@Override
	public <T> boolean all(final int i,
			final List<? extends T> list,
			final Predicate<? super T> predicate) throws InterruptedException {
		return listStart(i, list, (List<? extends T> lst) -> lst.stream().allMatch(predicate))
			.stream().allMatch(x -> x);
	}
	/*/
	@Override
	public <T> boolean all(final int i,
			final List<? extends T> list,
			final Predicate<? super T> predicate) throws InterruptedException {
		final MyAtomicBoolean interrupt = new MyAtomicBoolean(false);
		listStart(i, list, (List<? extends T> lst) -> {
			for (T e : lst) {
				if (!predicate.test(e)) {
					interrupt.set(true);
					break;
				}
				if (interrupt.get()) {
					break;
				}
			}
			return 0;
		});
		return !interrupt.get();
	}
	//*/

	@Override
	public <T> boolean any(final int i,
			final List<? extends T> list,
			final Predicate<? super T> predicate) throws InterruptedException {
		return !all(i, list, predicate.negate());
	}

	@Override
	public String join(final int i, final List<?> list) throws InterruptedException {
		final List<String> mapped = map(i, list, Object::toString);
		return String.join("", mapped);
	}

	private <U, T> List<U> streamHelper(final int i,
			final List<? extends T> list,
			final Function<Stream<? extends T>, Stream<? extends U>> func) throws InterruptedException {
		return listStart(i, list, (List<? extends T> lst) -> func.apply(lst.stream()))
			.stream()
			.flatMap(x -> x)
			.collect(Collectors.toList());
	}

	@Override
	public <T> List<T> filter(final int i,
			final List<? extends T> list,
			final Predicate<? super T> predicate) throws InterruptedException {
		return streamHelper(i, list, s -> s.filter(predicate));
	}

	@Override
	public <T, U> List<U> map(final int i,
			final List<? extends T> list,
			final Function<? super T, ? extends U> function) throws InterruptedException {
		return streamHelper(i, list, s -> s.map(function));
	}
}
