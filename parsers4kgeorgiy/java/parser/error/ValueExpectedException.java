package expression.parser.error;

public class ValueExpectedException extends ParserException {
    private static final long serialVersionUID = 46L;
    public ValueExpectedException() {
    }

    public ValueExpectedException(final String what) {
        super(what);
    }

    public ValueExpectedException(final String what, final int position) {
        super(what, position);
    }
}
