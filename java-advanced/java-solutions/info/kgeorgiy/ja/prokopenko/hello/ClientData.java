package info.kgeorgiy.ja.prokopenko.hello;

import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;

public class ClientData {
	private final String prefix;
	protected final int id;
	protected int counter = 0;
	// ByteBuffer.mark does not work since it is discarded on rewind/position
	private int mark;
	protected ByteBuffer buffer;
	private String lastText;

	public String getPrefix() {
		return prefix;
	}

	public ClientData(final String prefix, final int id) {
		this.id = id;
		this.prefix = prefix + id + "_";
	}

	public void initSendBuffer(int size) {
		buffer = ByteBuffer.wrap(new byte[size]);
		buffer.put(prefix.getBytes(StandardCharsets.UTF_8));
		mark = buffer.position();
	}

	public ByteBuffer makeSendBuffer() {
		final String suffix = Integer.toString(counter);
		lastText = prefix + suffix;
		buffer.position(mark);
		buffer.limit(buffer.array().length);
		buffer.put(suffix.getBytes(StandardCharsets.UTF_8));
		return buffer;
	}

	public int advance() {
		return ++counter;
	}

	public String checkAnswer(final byte[] buf, final int offset, final int length) {
		final String answerText = new String(buf, offset, length, StandardCharsets.UTF_8);
		final int position = answerText.indexOf(lastText);
		if (position == -1 || position + 1 < answerText.length() && Character.isDigit(answerText.charAt(position + 1))) {
			System.err.format("bad response: %s for %s%n", answerText, lastText);
			return null;
		}
		return answerText;
	}
}

