package rmi;

public class InvalidIdException extends RuntimeException {
	private static final int serialVersionUID = 30;
	public InvalidIdException(final String id) {
		super(id);
	}

	public static void verify(final String id) {
		if (id == null || id.indexOf(':') >= 0) {
			throw new InvalidIdException(id);
		}
	}
}
