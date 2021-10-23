package expression.parser.error;

public class ParserException extends Exception {
    private static final long serialVersionUID = 43L;
    private int position;
    public ParserException() {
        position = -1;
    }

    public ParserException(final String what, final int position) {
        super(what);
        this.position = position;
    }

    public ParserException(final String what) {
        this(what, -1);
    }

    public void setPosition(int position) {
        this.position = position;
    }

    public int getPosition() {
        return position;
    }

    @Override
    public String getMessage() {
        return super.getMessage() + " at (" + position + ") position in the expression";
    }
}
