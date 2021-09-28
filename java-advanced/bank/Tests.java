package rmi;

import org.junit.*;
import java.rmi.*;
import java.rmi.server.*;
import java.net.*;
import java.io.*;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;
import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;
import static org.junit.Assert.*;

public class Tests {
	private Bank client;
	private final static int port = 3030;
	private final static String BANK = "//localhost/bank";
	private final ProcessBuilder processBuilder;
	private Process process;
	private static final String CLASSPATH = getClassPath();

	private static interface ThrowingRunnable {
		void run() throws Exception;
	}

	private static String getClassPath() {
		try {
			return Path.of(Server.class.getProtectionDomain().getCodeSource().getLocation().toURI()).toString();
		} catch (final URISyntaxException e) {
			throw new AssertionError(e);
		}
	}

	public Tests() {
		processBuilder = new ProcessBuilder();
		processBuilder.command("java", "-cp", CLASSPATH, "rmi.Server", Integer.toString(port));
		processBuilder.environment().put("CLASSPATH", CLASSPATH);
		processBuilder.inheritIO();
	}

	private Exception assertThrows(final ThrowingRunnable r, boolean throwed) {
		try {
			r.run();
			assertTrue("expected throw", throwed == false);
			return null;
		} catch (final Exception ex) {
			assertTrue("unexpected throw", throwed == true);
			return ex;
		}
	}
	private Exception assertThrows(final ThrowingRunnable r) {
		return assertThrows(r, true);
	}

	@Before
	public void before() throws IOException {
		assertFalse("Already running", process != null && process.isAlive());
		process = processBuilder.start();

		try {
			for (int i = 0; i < 10; i++) {
				try {
					client = (Bank)Naming.lookup(BANK);
					System.err.println("bank found");
					break;
				} catch (final NotBoundException e) {
					System.err.println("bank not found, waiting...");
					Thread.sleep(500);
				}
			}
			if (client == null) {
				throw new RuntimeException("can't connect to the bank");
			}
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
			return;
		} catch (final RemoteException e) {
			throw new RuntimeException("remote excetpion", e);
		} catch (final MalformedURLException e) {
			throw new RuntimeException("Bank URL is invalid");
		}
	}

	@After
	public void after() {
		try {
			Naming.unbind(BANK);
		} catch (Exception ignored) {
		}
		client = null;
		if (process != null) {
			process.destroy();
			try {
				assertTrue(process.waitFor(2, TimeUnit.SECONDS));
				System.out.println("Server closed");
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
			process = null;
		}
	}

	@Test
	public void testCreate() throws RemoteException {
		assertTrue(client != null);
		final Person a1 = client.createPerson("411", "k", "p");
		final Person a2 = client.createPerson("411", "k", "p");
		assertTrue(a1.equals(a2));
		assertThrows(() -> { client.createPerson("411", "k", "k"); });
	}


	@Test
	public void testReCreate() throws RemoteException {
		final Person p = client.createPerson("411", "k", "p");
		final List<Account> accounts = new ArrayList<>();
		final Account a = p.createAccount("1");
		accounts.add(a);
		accounts.add(p.createAccount("1"));
		a.setAmount(30);
		accounts.add(p.createAccount("1"));
		accounts.add(p.findAccount("1"));
		accounts.add(client.createPerson("411", "k", "p").createAccount("1"));
		for (final Account acc : accounts) {
			assertEquals(acc.getAmount(), 30);
		}
		accounts.get(3).setAmount(3);
		for (final Account acc : accounts) {
			assertEquals(acc.getAmount(), 3);
		}
	}

	@Test
	public void testId() throws RemoteException {
		assertThrows(() -> { client.createPerson("a:b", "k", "p"); });
		assertThrows(() -> { client.createAccount("a:b"); });
	}

	private static boolean eq(final Account a, final Account b) throws RemoteException {
		return a.getId().equals(b.getId())
			&& a.getAmount() == b.getAmount();
	}
	private static boolean eq(final Person a, final Person b) throws RemoteException {
		if (!(a.getPassport().equals(b.getPassport())
				&& a.getName().equals(b.getName())
				&& a.getSurname().equals(b.getSurname()))) {
			return false;
		}
		final List<Account> i1 = a.getAccounts();
		final List<Account> i2 = b.getAccounts();
		if (i1.size() != i2.size()) {
			return false;
		}
		for (int i = 0 ; i < i1.size(); i++) {
			if (!eq(i1.get(i), i2.get(i))) {
				return false;
			}
		}
		return true;
	}

	private static void printPerson(final Person p) throws RemoteException {
		System.out.format("%s %s %s%n", p.getPassport(), p.getName(), p.getSurname());
		for (final Account acc : p.getAccounts()) {
			System.out.format("\t%s -> %d%n", acc.getId(), acc.getAmount());
		}
	}

	@Test
	public void testLocal() throws RemoteException {
		System.out.println("1");
		assertTrue(client != null);
		client.createPerson("1", "k", "p");
		final LocalPerson l1 = client.getLocalPerson("1");
		final LocalPerson l2 = client.getLocalPerson("1");
		final LocalPerson copy = l1.deepCopy();
		assertTrue(eq(copy, l2));
		final Person r1 = client.getRemotePerson("1");
		final Person r2 = client.getRemotePerson("1");
		assertTrue(eq(l1, l2));
		assertTrue(eq(l2, r1));
		assertTrue(eq(r1, r2));

		final Account ra1 = r1.createAccount("acc1");
		assertFalse(eq(l1, r2));
		assertTrue(eq(l1, l2));
		assertTrue(eq(r1, r2));

		ra1.setAmount(30);
		assertFalse(eq(l1, r2));
		assertTrue(eq(l1, l2));
		assertTrue(eq(r1, r2));
		assertEquals(r1.findAccount("acc1").getAmount(), 30);
		assertEquals(l1.findAccount("acc1"), null);

		final LocalPerson l3 = client.getLocalPerson("1");
		assertTrue(eq(l3, r1));

		l1.createAccount("acc2");
		assertTrue(eq(r1, r2));
		assertTrue(eq(r1, l3));
	}
}
