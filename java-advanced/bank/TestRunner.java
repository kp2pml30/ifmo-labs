package rmi;

import org.junit.runner.JUnitCore;
import org.junit.runner.Result;
import org.junit.runner.notification.Failure;

public class TestRunner {
	public static void main(final String[] args) {
		final Result result = JUnitCore.runClasses(Tests.class);
	
		for (final Failure failure : result.getFailures()) {
			System.out.println(failure.toString());
			final Throwable ex = failure.getException();
			if (ex != null) {
				System.out.println(ex.getMessage());
				ex.printStackTrace();
			}
		}
	
		if (result.wasSuccessful()) {
			System.out.println("success");
		} else {
			System.out.println("!! fail !!");
			System.exit(1);
		}
	}
}
