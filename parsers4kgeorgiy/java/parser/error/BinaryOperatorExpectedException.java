package expression.parser.error;

public class BinaryOperatorExpectedException extends ParserException {
    private static final long serialVersionUID = 42L;
    public BinaryOperatorExpectedException() {
    }

    public BinaryOperatorExpectedException(final String what) {
        super(what);
    }

    public BinaryOperatorExpectedException(final String what, final int position) {
        super(what, position);
    }
}
