package rmi;

import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.rmi.*;
import java.util.Map;

public class RemoteBank implements Bank {
	private final int port;
	private final ConcurrentMap<String, RemoteAccount> accounts = new ConcurrentHashMap<>();
	private final ConcurrentMap<String, RemotePerson> people = new ConcurrentHashMap<>();

	public RemoteBank(final int port) {
		this.port = port;
	}


	private class RemotePerson extends PersonStorage {
		public RemotePerson(final String name, final String surname, final String passport) {
			super(name, surname, passport);
		}

		public RemotePerson(final String name, final String surname, final String passport, final ConcurrentMap<String, RemoteAccount> accounts) {
			super(name, surname, passport, accounts);
		}

		@Override
		public Account createAccount(final String id) throws RemoteException {
			InvalidIdException.verify(id);
			final String nid = getAccountId(id);
			RemoteException[] exc = new RemoteException[1];
			final Account result = accounts.computeIfAbsent(nid, k -> {
				try {
					return RemoteBank.this.createAccountUnchecked(nid);
				} catch (RemoteException ex) {
					exc[0] = ex;
					return null;
				}
			});
			if (exc[0] != null) {
				throw exc[0];
			}
			return result;
		}
	}

	RemoteAccount createAccountUnchecked(final String id) throws RemoteException {
		System.out.println("Creating account " + id);
		final RemoteAccount account = new RemoteAccount(id);
		if (accounts.putIfAbsent(id, account) == null) {
			UnicastRemoteObject.exportObject(account, port);
			return account;
		} else {
			return getAccountUnchecked(id);
		}
	}

	RemoteAccount getAccountUnchecked(final String id) {
		System.out.println("Retrieving account " + id);
		return accounts.get(id);
	}

	@Override
	public Account createAccount(final String id) throws RemoteException {
		InvalidIdException.verify(id);
		return createAccountUnchecked(id);
	}

	@Override
	public Account getAccount(final String id) throws RemoteException {
		InvalidIdException.verify(id);
		return getAccountUnchecked(id);
	}

	@Override
	public LocalPerson getLocalPerson(final String passport) throws RemoteException {
		final RemotePerson person = people.get(passport);
		if (person == null) {
			return null;
		}
		return person.deepCopy();
	}
	@Override
	public Person getRemotePerson(final String passport) throws RemoteException {
		final RemotePerson person = people.get(passport);
		if (person == null) {
			return null;
		}
		return person;
	}

	@Override
	public Person createPerson(String passport, String name, String surname) throws RemoteException {

		final RemotePerson ifAbsent = new RemotePerson(name, surname, passport);
		final RemotePerson found = people.putIfAbsent(passport, ifAbsent);
		if (found == null) {
			UnicastRemoteObject.exportObject(ifAbsent, port);
			return ifAbsent;
		}
		if (!found.getName().equals(name) || !found.getSurname().equals(surname)) {
			throw new RuntimeException(String.format(
					"account redefinition with different credits %s :: new %s %s != was %s %s",
					passport,
					name, surname,
					found.getName(), found.getSurname()));
		}
		return found;
	}
}
