package info.kgeorgiy.ja.prokopenko.hello;

import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;

public class ServerData {
	// ByteBuffer.mark does not work since it is discarded on rewind/position
	protected int mark;
	protected final ByteBuffer buffer;

	public ServerData(int sendSize) {
		buffer = ByteBuffer.wrap(new byte[sendSize]);
		buffer.put("Hello, ".getBytes(StandardCharsets.UTF_8));
		mark = buffer.position();
	}

	public ByteBuffer getBuffer() {
		return buffer;
	}

	public ByteBuffer getSend() {
		buffer.limit(buffer.position());
		buffer.rewind();
		return buffer;
	}
	public ByteBuffer getWrite() {
		buffer.limit(buffer.array().length);
		buffer.position(mark);
		return buffer;
	}
}

