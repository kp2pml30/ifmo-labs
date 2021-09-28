package info.kgeorgiy.ja.prokopenko.hello;

import info.kgeorgiy.java.advanced.hello.HelloServer;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.channels.*;
import java.util.*;
import java.net.*;

public class HelloUDPNonblockingServer implements HelloServer {
	private Selector selector;
	private DatagramChannel channel;
	private Thread thread;
	private final Queue<ServerData> vacant = new ArrayDeque<>();
	private final Queue<ResponseTo> responses = new ArrayDeque<>();

	private static class ResponseTo {
		public final SocketAddress address;
		public final ServerData data;

		public ResponseTo(final SocketAddress address, final ServerData data) {
			this.address = address;
			this.data = data;
		}
	}

	void selectOccured(final SelectionKey key) {
		try {
			if ((key.interestOps() & SelectionKey.OP_READ) != 0 && key.isReadable()) {
				if (vacant.isEmpty()) {
					throw new IllegalStateException("bug, read with no buffers");
				}
				final ServerData data = vacant.poll();
				final SocketAddress address = channel.receive(data.getWrite());
				responses.offer(new ResponseTo(address, data));
				if (vacant.isEmpty()) {
					key.interestOps(SelectionKey.OP_WRITE);
				} else {
					key.interestOps(SelectionKey.OP_READ | SelectionKey.OP_WRITE);
				}
			} else if ((key.interestOps() & SelectionKey.OP_WRITE) != 0 && key.isWritable()) {
				if (responses.isEmpty()) {
					throw new IllegalStateException("bug, write with no responses");
				}
				final ResponseTo response = responses.poll();
				channel.send(response.data.getSend(), response.address);
				vacant.offer(response.data);
				if (responses.isEmpty()) {
					key.interestOps(SelectionKey.OP_READ);
				} else {
					key.interestOps(SelectionKey.OP_READ | SelectionKey.OP_WRITE);
				}
			}
		} catch (final IOException ex) {
			throw new UncheckedIOException(ex);
		}
	}

	private void go() {
		try {
			while (!Thread.interrupted()) {
				selector.select(this::selectOccured, 100);
			}
		} catch (final IOException ex) {
			throw new UncheckedIOException(ex);
		}
	}

	@Override
	public void start(final int port, final int threads) {
		try {
			selector = Selector.open();
			channel = DatagramChannel.open();

			final int sendSize = channel.socket().getReceiveBufferSize();
			for (int i = 0; i < threads; i++) {
				vacant.offer(new ServerData(sendSize));
			}

			channel.bind(new InetSocketAddress("localhost", port));
			channel.configureBlocking(false);
			channel.register(selector, SelectionKey.OP_READ, this);
			thread = new Thread(this::go);
			thread.start();
		} catch (IOException ex) {
			throw new UncheckedIOException(ex);
		}
	}

	@Override
	public void close() {
		thread.interrupt();
		try {
			thread.join();
		} catch (InterruptedException ex) {
			Thread.currentThread().interrupt();
		}
		vacant.clear();
		responses.clear();
		try {
			selector.close();
		} catch (IOException ex) {
			throw new UncheckedIOException(ex);
		}
		try {
			channel.close();
		} catch (IOException ex) {
			throw new UncheckedIOException(ex);
		}
	}

	public static void main(final String[] args) {
		HelloUDPServer.main(args, HelloUDPNonblockingServer.class);
	}
}
