package rmi;

import java.rmi.*;
import java.net.MalformedURLException;

public class PersonApp {
	private static void help() {
		System.err.format("PersonApp passport name surname account [amount]%nommit amount to set, otherwise get");
	}
	private static void doRemoteJob(final String[] args, final Integer amount) throws RemoteException {
		Bank bank = null;
		for (int i = 0; i < 10; i++) {
			try {
				bank = (Bank)Naming.lookup("//localhost/bank");
				System.err.println("bank found");
				break;
			} catch (final NotBoundException e) {
				System.err.println("bank not found, waiting...");
				try {
					Thread.sleep(500);
				} catch (InterruptedException ex) {
					return;
				}
			} catch (final MalformedURLException ex) {
				System.err.println(ex.getMessage());
				return;
			}
		}
		if (bank == null) {
			throw new RuntimeException("can't connect to the bank");
		}
		final Account account = bank.createPerson(args[0], args[1], args[2]).createAccount(args[3]);
		if (amount == null) {
			System.out.println(account.getAmount());
		} else {
			account.setAmount(amount);
			System.out.println("Set successfully");
		}
	}
	public static void main(final String[] args) {
		if (args.length > 5 || args.length < 4) {
			help();
			return;
		}
		final Integer amount;
		try {
			amount = args.length == 5 ? Integer.parseInt(args[4]) : null;
		} catch (final NumberFormatException ex) {
			help();
			return;
		}
		try {
			doRemoteJob(args, amount);
		} catch (final RemoteException ex) {
			System.out.format("remote exception%n%s%n", ex.toString());
		}
	}
}
