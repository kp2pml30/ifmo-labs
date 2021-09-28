package rmi;

import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.List;
import java.util.stream.Collectors;
import java.io.Serializable;

public abstract class PersonStorage implements Person, Serializable {
	protected final String name;
	protected final String surname;
	protected final String passport;
	protected final ConcurrentMap<String, RemoteAccount> accounts;

	public PersonStorage(final String name, final String surname, final String passport) {
		this(name, surname, passport, new ConcurrentHashMap<>());
	}

	public PersonStorage(final String name, final String surname, final String passport, final ConcurrentMap<String, RemoteAccount> accounts) {
		InvalidIdException.verify(passport);
		this.name = name;
		this.surname = surname;
		this.passport = passport;
		this.accounts = accounts;
	}

	protected String getAccountId(final String id) {
		InvalidIdException.verify(id);
		return passport + ":" + id;
	}

	@Override
	public String getName() {
		return name;
	}
	@Override
	public String getSurname() {
		return surname;
	}
	@Override
	public String getPassport() {
		return passport;
	}

	@Override
	public List<Account> getAccounts() {
		return accounts.values().stream().collect(Collectors.toList());
	}
	@Override
	public RemoteAccount findAccount(String id) {
		return accounts.get(getAccountId(id));
	}

	public LocalPerson deepCopy() {
		return new LocalPerson(name, surname, passport,
				accounts.entrySet().stream()
					.collect(Collectors
						.toConcurrentMap(
							k -> k.getKey(),
							v -> v.getValue().deepCopy())));
	}
}

