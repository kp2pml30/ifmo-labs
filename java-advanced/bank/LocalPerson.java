package rmi;

import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.ConcurrentHashMap;

public class LocalPerson extends PersonStorage {
	private final int serialUID = 30;

	public LocalPerson(final String name, final String surname, final String passport) {
		super(name, surname, passport);
	}

	public LocalPerson(final String name, final String surname, final String passport, final ConcurrentMap<String, RemoteAccount> accounts) {
		super(name, surname, passport, accounts);
	}

	@Override
	public RemoteAccount createAccount(final String id) {
		return accounts.computeIfAbsent(id, x -> new RemoteAccount(getAccountId(id)));
	}
}
