package info.kgeorgiy.ja.prokopenko.hello;

import info.kgeorgiy.java.advanced.hello.HelloClient;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.ByteBuffer;
import java.nio.channels.*;
import java.util.*;
import java.net.*;

public class HelloUDPNonblockingClient implements HelloClient {
	private int maxcounter;
	private boolean didSomething;
	private Map<Integer, SelectionKey> keys;

	private class Data extends ClientData {
		private ByteBuffer readBuffer;

		public Data(final String prefix, final int id) {
			super(prefix, id);
		}

		public void initReadBuffer(final int size) {
			readBuffer = ByteBuffer.wrap(new byte[size]);
		}

		private void interrupt(final SelectionKey key) {
			keys.remove(id);
			key.cancel();
		}

		public void read(final SelectionKey key, final DatagramChannel channel) throws IOException {
			key.interestOps(SelectionKey.OP_WRITE);
			readBuffer.rewind();

			channel.read(readBuffer);

			final String answerText = checkAnswer(readBuffer.array(), 0, readBuffer.position());

			if (answerText == null) {
				return;
			}
			System.out.println(answerText);

			if (advance() >= maxcounter) {
				interrupt(key);
			}
		}

		public void write(final SelectionKey key, final DatagramChannel channel) throws IOException {
			if (counter >= maxcounter) {
				throw new RuntimeException("wtf");
			}
			key.interestOps(SelectionKey.OP_READ);
			final ByteBuffer buffer = makeSendBuffer();
			buffer.limit(buffer.position());
			buffer.rewind();
			channel.write(buffer);
		}
	}

	private void selector(final SelectionKey key) {
		didSomething = true;
		try {
			final Data data = (Data)key.attachment();
			final DatagramChannel channel = (DatagramChannel)key.channel();

			if (key.interestOps() == SelectionKey.OP_READ) {
				data.read(key, channel);
			} else if (key.interestOps() == SelectionKey.OP_WRITE) {
				data.write(key, channel);
			} else {
				throw new RuntimeException("unexpected operation");
			}
		} catch (final IOException ex) {
			throw new UncheckedIOException(ex);
		}
	}

	private void throwingRun(final String host, final int port, final String prefix, final int threads, final int requests) throws IOException {
		final List<DatagramChannel> channels = new ArrayList<>();
		try (final Selector selector = Selector.open()) {
			maxcounter = requests;
			keys = new HashMap<>();
			for (int i = 0; i < threads; i++) {
				final DatagramChannel channel = DatagramChannel.open();
				channel.connect(new InetSocketAddress(host, port));
				channel.configureBlocking(false);
				channels.add(channel);

				final Data data = new Data(prefix, i);
				data.initSendBuffer(channel.socket().getSendBufferSize());
				data.initReadBuffer(channel.socket().getReceiveBufferSize());

				keys.put(i, channel.register(selector, SelectionKey.OP_WRITE, data));
			}

			while (!keys.isEmpty()) {
				didSomething = false;
				selector.select(this::selector, 200);
				if (!keys.isEmpty() && !didSomething) {
					for (final SelectionKey key : keys.values()) {
						key.interestOps(SelectionKey.OP_WRITE);
					}
				}
			}
		}
		for (final DatagramChannel channel : channels) {
			channel.close();
		}
	}

	@Override
	public void run(final String host, final int port, final String prefix, final int threads, final int requests) {
		try {
			throwingRun(host, port, prefix, threads, requests);
		} catch (final IOException ex) {
			throw new UncheckedIOException(ex);
		}
	}

	public static void main(final String[] args) {
		HelloUDPClient.main(args, HelloUDPNonblockingClient.class);
	}
}
