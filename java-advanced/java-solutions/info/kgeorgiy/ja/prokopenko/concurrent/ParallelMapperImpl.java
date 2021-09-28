package info.kgeorgiy.ja.prokopenko.concurrent;

import info.kgeorgiy.java.advanced.mapper.ParallelMapper;

import java.util.Collections;
import java.util.List;
import java.util.ArrayList;
import java.util.function.Function;
import java.util.function.Consumer;

public class ParallelMapperImpl implements ParallelMapper {
	private interface ObjectPool<T> {
		T borrow() throws InterruptedException;
		T borrowWait() throws InterruptedException;
		void put(T obj);
	}

	private static class ArrayObjectPool<T> implements ObjectPool<T> {
		// pool: взять **любой**, и у стека реализация проще (если на массиве, то не нужно делать кольцевой буффер/бакеты;
		//  а если linked, то кэш умирает).
		private final ArrayList<T> pool = new ArrayList<>();

		@Override
		public synchronized T borrow() throws InterruptedException {
			return pool.isEmpty() ? null : pool.remove(pool.size() - 1);
		}
		@Override
		public synchronized T borrowWait() throws InterruptedException {
			while (pool.isEmpty()) {
				wait();
			}
			return pool.remove(pool.size() - 1);
		}
		@Override
		public synchronized void put(T obj) {
			pool.add(obj);
			notify();
		}
	}

	private class WorkerThread extends Thread {
		public Runnable task = null;

		@Override
		public synchronized void run() {
			try {
				while (!Thread.currentThread().isInterrupted()) {
					while (task == null) {
						if (!running.get()) {
							return;
						}
						wait();
					}
					task.run();
					task = null;
					vacant.put(this);
				}
			} catch (InterruptedException ignored) {
				Thread.currentThread().interrupt();
			}
		}
	}

	private final MyAtomicBoolean running = new MyAtomicBoolean(true);
	private final ObjectPool<WorkerThread> vacant = new ArrayObjectPool<>();
	private final int threadsCount;

	public ParallelMapperImpl(int threads) {
		if (threads <= 0) {
			throw new IllegalArgumentException("number of threads must be > 0");
		}
		this.threadsCount = threads;
		while (threads-- > 0) {
			WorkerThread thread = new WorkerThread();
			thread.start();
			vacant.put(thread);
		}
	}

	private static class IntWrapper {
		public int value = 0;

		public synchronized void incrNotify() {
			value++;
			notify();
		}
	}

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
		List<R> result = new ArrayList<>();
		for (int i = 0; i < args.size(); i++) {
			result.add(null);
		}
		IntWrapper executed = new IntWrapper();
		for (int i = 0; i < args.size(); i++) {
			final int ii = i;
			final T arg = args.get(i);
			final WorkerThread thread = vacant.borrowWait();
			synchronized (thread) {
				thread.task = () -> {
					result.set(ii, f.apply(arg));
					executed.incrNotify();
				};
				thread.notify();
			}
		}
		synchronized (executed) {
			while (executed.value != args.size()) {
					executed.wait();
			}
		}
		return result;
	}

	public int threadsCount() {
		return threadsCount;
	}

	@Override
	public void close() {
		// how to handle iterrupts here?
		boolean interrupted = false;
		InterruptedException interExc = null;
		running.set(false);
		for (int i = 0; i < threadsCount(); i++) {
			final WorkerThread thread;
			try {
				thread = vacant.borrowWait();
			} catch (InterruptedException ex) {
				interrupted = true;
				i--;
				continue;
			}
			synchronized (thread) {
				thread.notify();
			}
			boolean done = false;
			while (!done)
			{
				try {
					thread.join();
					done = true;
				} catch (InterruptedException ex) {
					interrupted = true;
				}
			}
		}
		if (interrupted) {
			Thread.currentThread().interrupt();
		}
	}
}
