package expression.exceptions;

import expression.CommonExpression;

public class EvaluationException extends ArithmeticException {
    private final static long serialVersionUID = 49;
    private CommonExpression<?> where;

    public EvaluationException() {
    }

    public EvaluationException(String message) {
        super(message);
    }

    public void setWhere(CommonExpression<?> node) {
       where = node;
    }

    public CommonExpression<?> getWhere() {
       return where;
    }
}
