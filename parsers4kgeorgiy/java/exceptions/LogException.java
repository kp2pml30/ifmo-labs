package expression.exceptions;

public class LogException extends EvaluationException {
    private final static long serialVersionUID = 50;

    public LogException(String msg) {
        super(msg);
    }
}
