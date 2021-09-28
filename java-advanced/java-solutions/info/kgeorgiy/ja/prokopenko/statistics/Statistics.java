package info.kgeorgiy.ja.prokopenko.statistics;

public class Statistics<T, Average> {
	private final int count;
	private final int different;
	private final T min;
	private final T max;
	private final int minLen;
	private final int maxLen;
	private final Average average;

	public Statistics(int count, int different, T min, T max, int minLen, int maxLen, Average average) {
		this.count = count;
		this.different = different;
		this.min = min;
		this.max = max;
		this.minLen = minLen;
		this.maxLen = maxLen;
		this.average = average;
	}

	public int getCount() {
		return count;
	}

	public int getDifferent() {
		return different;
	}

	public T getMin() {
		return min;
	}

	public T getMax() {
		return max;
	}

	public int getMinLen() {
		return minLen;
	}

	public int getMaxLen() {
		return maxLen;
	}

	public Average getAverage() {
		return average;
	}
}
