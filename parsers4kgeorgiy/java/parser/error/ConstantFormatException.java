package expression.parser.error;

public class ConstantFormatException extends ParserException {
    private static final long serialVersionUID = 47L;
    public ConstantFormatException() {
    }

    public ConstantFormatException(final String what) {
        super(what);
    }

    public ConstantFormatException(final String what, final int position) {
        super(what, position);
    }
}
