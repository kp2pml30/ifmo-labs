package rmi;

import java.io.Serializable;

public class RemoteAccount implements Account, Serializable {
	private final String id;
	private int amount;

	protected RemoteAccount(final String id, final int amount) {
		this.id = id;
		this.amount = amount;
	}

	public RemoteAccount(final String id) {
		this(id, 0);
	}

	@Override
	public RemoteAccount deepCopy() {
		return new RemoteAccount(id, amount);
	}

	@Override
	public String getId() {
		return id;
	}

	@Override
	public synchronized int getAmount() {
		System.out.format("Getting amount of money for account %s -> %d%n", id, amount);
		return amount;
	}

	@Override
	public synchronized void setAmount(final int amount) {
		System.out.format("Setting amount of money for account %s <- %d%n", id, amount);
		this.amount = amount;
	}
}
