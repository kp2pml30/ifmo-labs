package info.kgeorgiy.ja.prokopenko.concurrent;

// may we use standart implementation?

public class MyAtomicBoolean {
	private volatile boolean value;

	public MyAtomicBoolean(boolean value) {
		this.value = value;
	}

	public boolean get() {
		return value;
	}
	public void set(boolean value) {
		this.value = value;
	}
}

