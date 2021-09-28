package info.kgeorgiy.ja.prokopenko.hello;

import java.net.DatagramSocket;
import java.net.DatagramPacket;
import java.net.SocketException;
import java.net.SocketTimeoutException;
import java.io.IOException;
import java.util.List;
import java.util.stream.Stream;
import java.util.stream.Collectors;
import java.nio.ByteBuffer;
import java.util.concurrent.Executors;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.TimeUnit;

import info.kgeorgiy.java.advanced.hello.HelloServer;

public class HelloUDPServer implements HelloServer {
	private DatagramSocket socket;
	private int maxPacketSendSize;
	private ExecutorService executor;
	private List<Worker> workers;

	private void connectTo(int port) {
		try {
			socket = new DatagramSocket(port);
			maxPacketSendSize = socket.getSendBufferSize();
		} catch (SocketException ex) {
			throw new RuntimeException("can't connect to port " + port, ex);
		}
	}

	public HelloUDPServer() {
	}

	private class Worker implements Runnable {
		private final ServerData data;

		public Worker(int sendSize) {
			data = new ServerData(sendSize);
		}

		@Override
		public void run() {
			final DatagramPacket packet = new DatagramPacket(new byte[maxPacketSendSize], maxPacketSendSize);
			while (!Thread.interrupted() && !socket.isClosed()) {
				try {
					socket.receive(packet);
				} catch (SocketTimeoutException ex) {
					continue;
				} catch (IOException ex) {
					if (socket.isClosed()) {
						return;
					}
					System.out.format("can't recv %s%n", ex.getMessage());
				}
				final ByteBuffer recvd = data.getWrite();
				recvd.put(packet.getData(), 0, packet.getLength());
				try {
					final ByteBuffer buffer = data.getSend();
					socket.send(new DatagramPacket(buffer.array(), 0, buffer.limit(), packet.getAddress(), packet.getPort()));
				} catch (IOException ex) {
					if (socket.isClosed()) {
						return;
					}
					System.out.format("can't send response %n%s%n", ex.getMessage());
				}
			}
		}
	}

	@Override
	public void start(int port, int threads) {
		connectTo(port);
		int size;
		try {
			size = socket.getSendBufferSize();
		} catch (final SocketException ex) {
			throw new RuntimeException(ex);
		}
		workers = Stream.generate(() -> new Worker(size)).limit(threads).collect(Collectors.toList());
		executor = Executors.newFixedThreadPool(threads);
		for (final Worker worker : workers) {
			executor.submit(worker);
		}
	}

	@Override
	public void close() {
		workers = null;
		socket.close();
		executor.shutdownNow();
		try {
			executor.awaitTermination(10, TimeUnit.DAYS);
		} catch (final InterruptedException ex) {
			Thread.currentThread().interrupt();
		}
	}

	private static void help(final Class<?> clazz) {
		System.err.format("%s port threads%n", clazz.getName());
	}

	public static void main(final String[] args, final Class<?> clazz) {
		if (args.length != 2) {
			help(clazz);
			return;
		}
		final int port;
		final int threads;
		try {
			port = Integer.parseInt(args[0]);
			threads = Integer.parseInt(args[1]);
		} catch (final NumberFormatException ex) {
			help(clazz);
			System.err.println("can't parse <int> argument");
			System.err.println(ex.getMessage());
			return;
		}
		try (final HelloServer server = (HelloServer)clazz.getConstructor().newInstance()) {
			server.start(port, threads);
			while (!Thread.interrupted()) {
				try {
					Thread.sleep(1000);
				} catch (final InterruptedException ex) {
					return;
				}
			}
		} catch (final NoSuchMethodException | InstantiationException | IllegalAccessException | java.lang.reflect.InvocationTargetException ex) {
			System.err.format("can't create implementation from token: %s%n%s%n", clazz.getName(), ex.getMessage());
			return;
		}
	}

	public static void main(final String[] args) {
		main(args, HelloUDPServer.class);
	}
}
