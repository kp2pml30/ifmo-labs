package expression.exceptions;

public class PowException extends EvaluationException {
    private final static long serialVersionUID = 50;

    public PowException(String msg) {
       super(msg);
    }
}
