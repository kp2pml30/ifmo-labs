package info.kgeorgiy.ja.prokopenko.crawler;

import info.kgeorgiy.java.advanced.crawler.*;

import java.util.stream.Collectors;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.Executors;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Semaphore;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.TimeUnit;
import java.io.IOException;
import java.util.function.BiFunction;
import java.util.List;
import java.util.Queue;
import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.HashMap;
import java.util.ArrayList;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.net.MalformedURLException;

public class WebCrawler implements Crawler {
	private final int perHost;
	private final Downloader downloader;
	private final ExecutorService downloaders;
	private final ExecutorService extractors;

	public WebCrawler(final Downloader downloader, final int downloaders, final int extractors, final int perHost) {
		if (downloader == null || downloaders < 1 || extractors < 1 || perHost < 1) {
			throw new IllegalArgumentException("test (downloader == null || downloaders < 1 || extractors < 1 || perHost < 1) failed");
		}
		this.perHost = perHost;
		this.downloader = downloader;
		this.downloaders = Executors.newFixedThreadPool(downloaders);
		this.extractors = Executors.newFixedThreadPool(extractors);
	}


	private static <T> Set<T> newConcurrentSet() {
		return Collections.newSetFromMap(new ConcurrentHashMap<T, Boolean>());
	}

	private static interface ThrowingInterruptedRunnable {
		void run() throws InterruptedException;
	}
	private static class UncheckedInterruptedException extends RuntimeException {
		public UncheckedInterruptedException(InterruptedException ex) {
			super(ex);
		}

		public static Runnable wrap(ThrowingInterruptedRunnable func) {
			return () -> {
				try {
					func.run();
				} catch (InterruptedException ex) {
					throw new UncheckedInterruptedException(ex);
				}
			};
		}
	}

	private class Implementation {
		public CountDownLatch tasksCount;
		public final Set<String> visited = newConcurrentSet();
		public final Map<String, IOException> errors = new ConcurrentHashMap<>();

		// BFS
		public final Set<String> next2Download = newConcurrentSet();
		public final Map<String, Semaphore> threadsPerHost = new ConcurrentHashMap<>();

		private void decrementAtomicNotify(final AtomicInteger i) {
			if (i.decrementAndGet() == 0) {
				synchronized (i) {
					i.notify();
				}
			}
		}

		private void extract(final String url, final Document document) {
			try {
				final List<String> lst;
				try {
					lst = document.extractLinks();
				} catch (IOException ex) {
					errors.put(url, ex);
					return;
				}
				for (final String newUrl : lst) {
					if (visited.contains(newUrl)) {
						continue;
					}
					next2Download.add(newUrl);
				}
			} finally {
				tasksCount.countDown();
			}
		}

		private void download(final String url) throws InterruptedException {
			Semaphore hostCnt = null;
			try {
				final String host = URLUtils.getHost(url);
				hostCnt = threadsPerHost.computeIfAbsent(host, x -> new Semaphore(perHost));
			} catch (MalformedURLException ex) {
				errors.put(url, ex);
				return;
			}
			hostCnt.acquire();

			try {
				final Document document;
				if (!visited.add(url)) {
					tasksCount.countDown();
					return;
				}
				try {
					document = downloader.download(url);
				} catch (IOException ex) {
					errors.put(url, ex);
					tasksCount.countDown();
					return;
				}
				// no change in tasks count
				extractors.submit(() -> extract(url, document));
			} finally {
				hostCnt.release();
			}
		}

		private void schedule(final List<String> next) throws InterruptedException {
			tasksCount = new CountDownLatch(next.size());
			for (final String url : next) {
				try {
					downloaders.submit(UncheckedInterruptedException.wrap(() -> download(url)));
				} catch (final UncheckedInterruptedException ex) {
					Thread.currentThread().interrupt();
					return;
				}
			}
			return;
		}

		private boolean downloadLevel() throws InterruptedException {
			if (next2Download.isEmpty()) {
				return false;
			}
			final List<String> next = new ArrayList<>(next2Download);
			next2Download.clear();
			schedule(next);
			tasksCount.await();
			return true;
		}
		private void downloadLevels(final String root, final int depth) throws InterruptedException {
			next2Download.add(root);
			for (int i = 0; i < depth; i++) {
				if (!downloadLevel()) {
					break;
				}
			}
		}
	}

	@Override
	public Result download(final String url, final int depth) {
		final Implementation impl = new Implementation();
		try {
			impl.downloadLevels(url, depth);
		} catch (InterruptedException ex) {
			Thread.currentThread().interrupt();
		}
		return new Result(
				impl.visited.stream()
					.filter(x -> !impl.errors.containsKey(x))
					.collect(Collectors.toList()),
				impl.errors);
	}
	@Override
	public void close() {
		downloaders.shutdown();
		extractors.shutdown();
		try {
			downloaders.awaitTermination(5, TimeUnit.SECONDS);
			extractors.awaitTermination(5, TimeUnit.SECONDS);
		} catch (final InterruptedException ex) {
			Thread.currentThread().interrupt();
		}
	}

	private static void showHelp() {
		System.err.println("url [depth=1 [downloaders=8 [etractors=downloaders [perhost=downloaders]]]]");
	}
	public static void main(String[] args) {
		if (args == null || args.length < 1 || args.length > 5) {
			showHelp();
			return;
		}
		final Crawler crawler;
		final String url = args[0];
		final int depth;
		try {
			final int len = args.length;
			final BiFunction<Integer, Integer, Integer> get = (i, dflt) -> (len > i ? Integer.parseInt(args[i]) : dflt);
			depth = get.apply(1, 1);
			final int downloaders = get.apply(2, 8);
			final int extractors = get.apply(3, downloaders);
			final int perHost = get.apply(4, downloaders);
			crawler = new WebCrawler(new CachingDownloader(), downloaders, extractors, perHost);
		} catch (NumberFormatException | IOException ex) {
			System.err.println("can't parse");
			showHelp();
			System.err.println(ex);
			return;
		} catch (IllegalArgumentException ex) {
			System.err.println("can't create WebCrawler");
			showHelp();
			System.err.println(ex);
			return;
		}
		final Result res = crawler.download(url, depth);
		final var errors = res.getErrors();
		if (errors.size() != 0) {
			System.out.format("%d errors occured%n", errors.size());
			int counter = 0;
			for (final var i : errors.entrySet()) {
				System.out.format("%d) %s -> %s%n", ++counter, i.getKey(), i.getValue().toString());
			}
		}
		System.out.format("successfully downloaded %d pages%n", res.getDownloaded().size());
	}
}
