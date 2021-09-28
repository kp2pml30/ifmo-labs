package info.kgeorgiy.ja.prokopenko.hello;

import info.kgeorgiy.java.advanced.hello.HelloClient;

import java.net.DatagramSocket;
import java.net.DatagramPacket;
import java.net.SocketException;
import java.net.SocketTimeoutException;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.ByteBuffer;
import java.util.function.Consumer;
import java.util.List;
import java.util.stream.Stream;
import java.util.stream.Collectors;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class HelloUDPClient implements HelloClient {
	private static class Implementation {
		private final InetAddress host;
		private final int port;
		private final String prefix;
		private final int threads;
		private final int requests;

		private final AtomicInteger lastThreadId = new AtomicInteger(0);

		public Implementation(final String host, final int port, final String prefix, final int threads, final int requests) {
			try {
				this.host = InetAddress.getByName(host);
			} catch (UnknownHostException ex) {
				System.err.format("Can not parse host:: %s%n", host);
				System.err.println(ex.getMessage());
				throw new RuntimeException(ex);
			}
			this.port = port;
			this.prefix = prefix;
			this.threads = Math.max(1, threads);
			this.requests = requests;
		}

		private DatagramSocket makeConnected() {
			final DatagramSocket socket;
			try {
				socket = new DatagramSocket();
				socket.connect(host, port);
				socket.setSoTimeout(50);
			} catch (SocketException ex) {
				System.err.format("Can not connect:: %s:%d%n", host.toString(), port);
				System.err.println(ex.getMessage());
				throw new RuntimeException(ex);
			}
			return socket;
		}

		private class MyThread extends ClientData implements AutoCloseable, Runnable {
			public final DatagramSocket socket;
			private final Consumer<MyThread> task;
			private final DatagramPacket answer;
			private final DatagramPacket packet;

			public MyThread(final Consumer<MyThread> task) {
				super(prefix, lastThreadId.getAndIncrement());
				packet  = new DatagramPacket(new byte[0], 0, host, port);
				socket = makeConnected();
				final int answerLength;
				try {
					answerLength = socket.getReceiveBufferSize();
					initSendBuffer(socket.getSendBufferSize());
				} catch (final SocketException ex) {
					throw new RuntimeException(ex);
				}
				this.task = task;
				answer = new DatagramPacket(new byte[answerLength], answerLength);
			}

			@Override
			public void run() {
				while (counter < requests) {
					task.accept(this);
					advance();
				}
			}

			@Override
			public void close() {
				socket.close();
			}

			private void send() {
				try {
					ByteBuffer buf = makeSendBuffer();
					packet.setData(buf.array(), 0,buf.position());
					packet.setPort(port);
					packet.setAddress(host);
					while (true) {
							socket.send(packet);
							try {
								socket.receive(answer);
							} catch (final SocketTimeoutException ex) {
								continue;
							}
							final String answerText = checkAnswer(answer.getData(), 0, answer.getLength());
							if (answerText == null) {
								continue;
							}
							System.out.println(answerText);
							break;
					}
				} catch (final IOException ex) {
					throw new UncheckedIOException("can't send message", ex);
				}
			}
		}

		public void run() {
			System.out.format("threads=%d requests=%d%n", threads, requests);
			final Consumer<MyThread> task = MyThread::send;
			final ExecutorService executor = Executors.newFixedThreadPool(threads);
			final List<MyThread> infos = Stream.generate(() -> new MyThread(task)).limit(threads).collect(Collectors.toList());
			for (final MyThread info : infos) {
				executor.submit(info);
			}
			executor.shutdown();
			try {
				if (!executor.awaitTermination(10, TimeUnit.DAYS)) {
					executor.shutdownNow();
				}
			} catch (final InterruptedException ex) {
				Thread.currentThread().interrupt();
			}
			for (final MyThread info : infos) {
				info.close();
			}
		}
	}
	@Override
	public void run(final String host, final int port, final String prefix, final int threads, final int requests) {
		new Implementation(host, port, prefix, threads, requests).run();
	}

	private static void help(final Class<?> clazz) {
		System.err.println(clazz.getName() + " host port prefix threads requestsPerThread");
	}
	public static void main(final String[] args, final Class<?> clazz) {
		if (args.length != 5) {
			help(clazz);
			return;
		}
		final String host = args[0];
		final int port;
		final String prefix = args[2];
		final int threads;
		final int requests;
		try {
			port = Integer.parseInt(args[1]);
			threads = Integer.parseInt(args[3]);
			requests = Integer.parseInt(args[4]);
		} catch (final NumberFormatException ex) {
			help(clazz);
			System.err.println("can't parse <int> argument");
			System.err.println(ex.getMessage());
			return;
		}
		final HelloClient client;
		try {
			client = (HelloClient)clazz.getConstructor().newInstance();
		} catch (final NoSuchMethodException | InstantiationException | IllegalAccessException | java.lang.reflect.InvocationTargetException ex) {
			System.err.format("can't create implementation from token: %s%n%s%n", clazz.getName(), ex.getMessage());
			return;
		}
		client.run(host, port, prefix, threads, requests);
	}

	public static void main(final String[] args) {
		main(args, HelloUDPClient.class);
	}
}
