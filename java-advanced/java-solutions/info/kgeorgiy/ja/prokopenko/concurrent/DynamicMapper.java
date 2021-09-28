package info.kgeorgiy.ja.prokopenko.concurrent;

import info.kgeorgiy.java.advanced.mapper.ParallelMapper;

import java.util.List;
import java.util.ArrayList;
import java.util.function.Function;

public class DynamicMapper implements ParallelMapper {
	@Override
	public <T, R> List<R> map(
			final Function<? super T, ? extends R> f,
			final List<? extends T> args
	) throws InterruptedException {
		if (args.size() <= 0) {
			return List.of();
		}
		if (args.size() == 1) {
			return List.of(f.apply(args.get(0)));
		}
		final List<Thread> threadsList = new ArrayList<Thread>();
		final List<R> result = new ArrayList<>();
		for (int i = 0; i < args.size(); i++) {
			result.add(null);
		}
		for (int i = 0; i < args.size(); i++) {
			final int ii = i;
			final T arg = args.get(i);
			Thread thread = new Thread(() -> result.set(ii, f.apply(arg)));
			thread.start();
			threadsList.add(thread);
		}
		for (Thread thread : threadsList) {
			thread.join();
		}
		return result;
	}

	@Override
	public void close() {
	}
}
